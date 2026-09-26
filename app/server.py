"""LTL 联锁复核 HTTP 服务（Python 标准库，零第三方依赖）。

路由：
  POST /checks                      提交复核；成功才分配编号并落审计，非法输入 400 且无审计
  GET  /checks/<id>                 按编号读取成立结论或违规套索证据
  POST /checks/<id>/suppressions    对已判「不成立」的复核发起最小切换抑制审计
  GET  /suppressions/<id>           按审计编号读取最小切换抑制审计（重启后仍可读）
  GET  /health                      健康检查

复核记录会保存规程（位置/切换/命题）与公式，供抑制审计从保存的规程和公式
重新构造否定 GBA 乘积；原复核与规程一经保存不被改写。

端口由环境变量 ``LTL_PORT`` 指定（默认 8080），数据目录由
``LTL_DATA_DIR`` 指定（默认 /data）。
"""

from __future__ import annotations

import json
import os
import re
import threading
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from typing import Any, Dict, Optional

from .checker import check, push_negation
from .storage import AuditStore
from .suppression import NoFeasibleSuppression, minimize_suppression
from .validation import ValidationError, validate_request

_MAX_BODY = 4 * 1024 * 1024
_ID_RE = re.compile(r"^/checks/([A-Za-z0-9_-]+)$")
_SUPPRESS_RE = re.compile(r"^/checks/([A-Za-z0-9_-]+)/suppressions$")
_SUP_ID_RE = re.compile(r"^/suppressions/([A-Za-z0-9_-]+)$")


def build_record(spec: Dict[str, Any]) -> Dict[str, Any]:
    result = check(spec)
    neg_nnf = push_negation(spec["formula_ast"], neg=True)
    record: Dict[str, Any] = {
        "formula": spec["formula"],
        "initial": spec["initial"],
        # 保存规程与公式（抑制审计据此重构乘积；保存后不改写）
        "spec": {
            "locations": list(spec["locations"]),
            "initial": spec["initial"],
            "switches": [dict(sw) for sw in spec["switches"]],
            "propositions": {
                loc: list(props) for loc, props in spec["propositions"].items()
            },
            "formula": spec["formula"],
        },
        "holds": result.holds,
        "normalization": {
            "negation_nnf": neg_nnf.to_str(),
            "method": "否定公式广义 Büchi 自动机（tableau）× 规程乘积 × 接受 SCC",
        },
        "stats": result.stats,
        "violation": result.violation,
    }
    return record


class Handler(BaseHTTPRequestHandler):
    server_version = "LTLInterlock/1.0"

    # ---- 注入的共享件 ----
    store: AuditStore = None  # type: ignore[assignment]
    suppression_store: AuditStore = None  # type: ignore[assignment]

    def log_message(self, fmt: str, *args: Any) -> None:
        # 结构化一行日志
        import datetime
        ts = datetime.datetime.now(datetime.timezone.utc).isoformat()
        print(f"[{ts}] {self.address_string()} {fmt % args}", flush=True)

    # ---- 工具 ----
    def _send_json(self, status: int, payload: Dict[str, Any]) -> None:
        body = json.dumps(payload, ensure_ascii=False).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _read_json(self) -> Optional[Dict[str, Any]]:
        try:
            length = int(self.headers.get("Content-Length", "0"))
        except ValueError:
            self._send_json(400, {"error": "bad_request",
                                  "errors": ["Content-Length 非法"]})
            return None
        if length <= 0 or length > _MAX_BODY:
            self._send_json(400, {"error": "bad_request",
                                  "errors": ["请求体为空或超过 4MiB 限制"]})
            return None
        raw = self.rfile.read(length)
        try:
            payload = json.loads(raw.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            self._send_json(400, {"error": "bad_json",
                                  "errors": [f"JSON 解析失败: {exc}"]})
            return None
        if not isinstance(payload, dict):
            self._send_json(400, {"error": "bad_request",
                                  "errors": ["请求体必须是 JSON 对象"]})
            return None
        return payload

    # ---- 路由 ----
    def do_GET(self) -> None:  # noqa: N802
        path = self.path.split("?", 1)[0]
        if path == "/health":
            self._send_json(200, {"status": "ok"})
            return
        m = _ID_RE.match(path)
        if m:
            record = self.store.get(m.group(1))
            if record is None:
                self._send_json(404, {"error": "not_found",
                                      "errors": [f"编号 {m.group(1)} 不存在"]})
                return
            self._send_json(200, record)
            return
        m = _SUP_ID_RE.match(path)
        if m:
            record = self.suppression_store.get(m.group(1))
            if record is None:
                self._send_json(404, {"error": "not_found",
                                      "errors": [f"审计编号 {m.group(1)} 不存在"]})
                return
            self._send_json(200, record)
            return
        self._send_json(404, {"error": "not_found", "errors": ["未知路径"]})

    def do_POST(self) -> None:  # noqa: N802
        path = self.path.split("?", 1)[0]
        m = _SUPPRESS_RE.match(path)
        if m:
            self._create_suppression(m.group(1))
            return
        if path != "/checks":
            self._send_json(404, {"error": "not_found", "errors": ["未知路径"]})
            return
        payload = self._read_json()
        if payload is None:
            return
        try:
            spec = validate_request(payload)
        except ValidationError as exc:
            # 非法输入：定位拒绝，不生成审计编号
            self._send_json(400, {
                "error": "validation_failed",
                "errors": exc.errors,
            })
            return
        try:
            record = build_record(spec)
        except Exception as exc:  # 检测器内部错误不应吞掉
            self._send_json(500, {"error": "checker_fault",
                                  "errors": [f"{type(exc).__name__}: {exc}"]})
            return
        audit_id = self.store.save(record)
        record_out = {"id": audit_id, **record}
        self._send_json(201, record_out)

    # ---- 最小切换抑制审计 ----
    def _create_suppression(self, check_id: str) -> None:
        record = self.store.get(check_id)
        if record is None:
            self._send_json(404, {
                "error": "not_found",
                "errors": [f"来源复核编号 {check_id} 不存在"],
            })
            return
        if record.get("holds") is not False:
            self._send_json(409, {
                "error": "source_already_holds",
                "errors": [
                    f"来源复核 {check_id} 的结论为成立，"
                    "不存在需要抑制的违规执行，不创建审计"
                ],
            })
            return
        base_spec = record.get("spec")
        if not isinstance(base_spec, dict):
            self._send_json(422, {
                "error": "spec_unavailable",
                "errors": [
                    f"来源复核 {check_id} 未保存规程，"
                    "无法重新构造否定 GBA 乘积，不创建审计"
                ],
            })
            return
        try:
            outcome = minimize_suppression(base_spec)
        except NoFeasibleSuppression as exc:
            self._send_json(422, {
                "error": "no_feasible_suppression",
                "errors": [str(exc)],
            })
            return
        except Exception as exc:  # 检测器内部错误不应吞掉
            self._send_json(500, {"error": "checker_fault",
                                  "errors": [f"{type(exc).__name__}: {exc}"]})
            return
        # 修复后结论与可复算的最终证明：对禁用后规程重跑完整复核
        post = build_record(validate_request(outcome.reduced_payload))
        if not post["holds"]:  # 逻辑不可达：分支定界只接受复核成立的候选
            self._send_json(500, {
                "error": "checker_fault",
                "errors": ["修复后复核未成立，审计中止"],
            })
            return
        audit = {
            "kind": "switch_suppression_audit",
            "source_check_id": check_id,
            "formula_summary": {
                "formula": record["formula"],
                "negation_nnf": record["normalization"]["negation_nnf"],
                "initial": record["initial"],
            },
            "min_disabled_count": len(outcome.disabled),
            "disabled_switches": outcome.disabled,
            "post_repair": {
                "holds": post["holds"],
                "conclusion": (
                    "临时禁用上述切换后，同一初态起的所有无限执行"
                    "均满足原公式（完整判定，非有限回放）"
                ),
                "normalization": post["normalization"],
                "stats": post["stats"],
            },
            "proof": {
                "method": (
                    "分支定界：可达接受套索 → 必须命中的切换冲突集，"
                    "逐候选重构否定 GBA 乘积复核，取全局最少"
                ),
                "reduced_procedure": post["spec"],
                "final_check": {
                    "holds": post["holds"],
                    "normalization": post["normalization"],
                    "stats": post["stats"],
                },
                "search": {
                    "candidates_evaluated": outcome.candidates_evaluated,
                    "lassos_eliminated": outcome.lassos_eliminated,
                    "tie_break": "同样大小的可行修复按切换标识升序序列取字典序最小",
                },
                "recomputable": (
                    "以 proof.reduced_procedure 重新提交复核（POST /checks）"
                    "可复算同一成立结论（最终证明）"
                ),
            },
        }
        audit_id = self.suppression_store.save(audit)
        self._send_json(201, {"id": audit_id, **audit})


def create_server(host: str, port: int, data_dir: str) -> ThreadingHTTPServer:
    store = AuditStore(data_dir)
    suppression_store = AuditStore(
        data_dir, filename="suppressions.json", prefix="SUP"
    )
    handler = type(
        "BoundHandler",
        (Handler,),
        {"store": store, "suppression_store": suppression_store},
    )
    httpd = ThreadingHTTPServer((host, port), handler)
    httpd.daemon_threads = True
    return httpd


def main() -> None:
    host = os.environ.get("LTL_HOST", "0.0.0.0")
    port = int(os.environ.get("LTL_PORT", "8080"))
    data_dir = os.environ.get("LTL_DATA_DIR", "/data")
    httpd = create_server(host, port, data_dir)
    print(f"LTL 联锁复核服务监听 {host}:{port}，数据目录 {data_dir}", flush=True)
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        httpd.server_close()


if __name__ == "__main__":
    main()
