#!/usr/bin/env python3
"""Compose verify 服务入口：

1. 构建检查：全部源码可编译（字节码语法检查）；
2. 代码测试：unittest 全量用例（含永不放行违规闭环检测与最小切换抑制审计）；
3. HTTP 冒烟：健康检查、成立结论、违规闭环证据、非法请求 400 且无审计、编号读取、
   两条替代违规环的最小切换抑制审计（含可复算证明）与原有读取回归。

任一步失败即以非零退出码退出。
"""
import json
import os
import py_compile
import sys
import unittest
import urllib.error
import urllib.request

BASE = os.environ.get("LTL_BASE_URL", "http://ltl:8080")
FAILURES = []


def section(title):
    print(f"\n=== {title} ===", flush=True)


def check(name, cond, detail=""):
    mark = "PASS" if cond else "FAIL"
    print(f"[{mark}] {name}{(' — ' + detail) if detail and not cond else ''}",
          flush=True)
    if not cond:
        FAILURES.append(name)


def http(method, path, payload=None):
    data = None
    headers = {}
    if payload is not None:
        data = json.dumps(payload).encode("utf-8")
        headers["Content-Type"] = "application/json"
    req = urllib.request.Request(BASE + path, data=data, headers=headers,
                                 method=method)
    try:
        with urllib.request.urlopen(req, timeout=10) as resp:
            return resp.status, json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as exc:
        return exc.code, json.loads(exc.read().decode("utf-8"))


# 永不放行（饥饿）闭环：request 出现后可不经 granted 直接返回
STARVATION = {
    "locations": ["idle", "req", "deny", "grant"],
    "initial": "idle",
    "switches": [
        {"id": "t1", "source": "idle", "target": "req"},
        {"id": "t2", "source": "req", "target": "idle"},
        {"id": "t3", "source": "req", "target": "deny"},
        {"id": "t4", "source": "deny", "target": "idle"},
        {"id": "tg", "source": "grant", "target": "idle"},
    ],
    "propositions": {
        "idle": [],
        "req": ["request"],
        "deny": ["denied"],
        "grant": ["granted"],
    },
    "formula": "G(!request | F granted)",
}

COMPLIANT = {
    "locations": ["idle", "req", "grant"],
    "initial": "idle",
    "switches": [
        {"id": "t1", "source": "idle", "target": "req"},
        {"id": "t2", "source": "req", "target": "grant"},
        {"id": "t3", "source": "grant", "target": "idle"},
    ],
    "propositions": {"idle": [], "req": ["request"],
                     "grant": ["request", "granted"]},
    "formula": "G(!request | F granted)",
}

# 两条替代违规环：idle→req→idle（t1,q1 迟发环）与 req→hold→req（d1,d2 悬置环）。
# {t1} 虽同时命中两环但会令 idle 失去全部外出切换（禁止）；
# 全局最少修复为 {d1,q1} 与 {d2,q1}，升序稳定裁决取 ["d1","q1"]。
TWO_LOOPS = {
    "locations": ["idle", "req", "hold", "grant"],
    "initial": "idle",
    "switches": [
        {"id": "t1", "source": "idle", "target": "req"},
        {"id": "d1", "source": "req", "target": "hold"},
        {"id": "d2", "source": "hold", "target": "req"},
        {"id": "e1", "source": "req", "target": "grant"},
        {"id": "e2", "source": "hold", "target": "grant"},
        {"id": "q1", "source": "req", "target": "idle"},
        {"id": "t6", "source": "grant", "target": "idle"},
    ],
    "propositions": {
        "idle": [], "req": ["request"], "hold": ["request"],
        "grant": ["granted"],
    },
    "formula": "G(!request | F granted)",
}


def main():
    # 1. 构建检查
    section("构建检查 py_compile")
    compile_ok = True
    app_dir = os.path.join(os.path.dirname(__file__), "..", "app")
    for name in sorted(os.listdir(app_dir)):
        if name.endswith(".py"):
            path = os.path.join(app_dir, name)
            try:
                py_compile.compile(path, doraise=True)
                print(f"[PASS] compile {name}", flush=True)
            except py_compile.PyCompileError as exc:
                compile_ok = False
                print(f"[FAIL] compile {name}: {exc}", flush=True)
    check("全部源码编译通过", compile_ok)

    # 2. 代码测试
    section("代码测试 unittest")
    root = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
    sys.path.insert(0, root)
    loader = unittest.TestLoader()
    suite = loader.discover(os.path.join(root, "tests"), top_level_dir=root)
    runner = unittest.TextTestRunner(verbosity=1)
    result = runner.run(suite)
    check("单元测试全部通过", result.wasSuccessful(),
          f"{len(result.failures)+len(result.errors)} 个失败")

    # 3. HTTP 冒烟
    section("HTTP 冒烟")
    status, body = http("GET", "/health")
    check("GET /health 200 ok", status == 200 and body.get("status") == "ok",
          f"status={status}")

    status, body = http("POST", "/checks", COMPLIANT)
    ok_id = body.get("id")
    check("合规规程 POST /checks 201 且 holds=true",
          status == 201 and body.get("holds") is True and ok_id,
          f"status={status} body={body}")

    status, body = http("GET", f"/checks/{ok_id}")
    check("按编号读取成立结论",
          status == 200 and body.get("id") == ok_id
          and body.get("holds") is True,
          f"status={status}")
    check("记录含否定 NNF 与自动机方法说明",
          "negation_nnf" in body.get("normalization", {}),
          str(body.get("normalization")))

    status, body = http("POST", "/checks", STARVATION)
    starv_id = body.get("id")
    v = body.get("violation") or {}
    steps = v.get("steps", [])
    m = v.get("loop_start_index")
    loop_locs = [s.get("location") for s in steps[m:]] if m is not None else []
    loop_false = all(s.get("formula_true_here") is False
                     for s in steps[m:]) if m is not None else False
    evidence_ok = all(
        isinstance(s.get("subformula_truth"), dict)
        and s.get("switch_taken") for s in steps
    )
    check("永不放行违规闭环 POST 201 且 holds=false",
          status == 201 and body.get("holds") is False and v,
          f"status={status}")
    check("闭环经过 request 且不经过 granted",
          "req" in loop_locs and "grant" not in loop_locs,
          f"loop_locs={loop_locs}")
    check("闭环上公式逐点为假（无限违规，非有限回放）", loop_false)
    check("每步含位置/切换/子式真值证据", evidence_ok)
    check("违规同样保存并可按编号读取",
          body.get("id") and http("GET", f"/checks/{body['id']}")[0] == 200)

    bad = json.loads(json.dumps(STARVATION))
    bad["switches"] = bad["switches"][:2]  # deny/grant 变死端
    status, body = http("POST", "/checks", bad)
    check("死端请求 400 且不分配编号",
          status == 400 and "id" not in body
          and any("死端" in e for e in body.get("errors", [])),
          f"status={status} body={body}")

    bad2 = json.loads(json.dumps(COMPLIANT))
    bad2["switches"][0]["target"] = "ghost"
    status, body = http("POST", "/checks", bad2)
    check("悬空端点 400 定位拒绝",
          status == 400 and any("悬空端点" in e for e in body.get("errors", [])))

    bad3 = json.loads(json.dumps(COMPLIANT))
    bad3["formula"] = "request U granted"
    status, body = http("POST", "/checks", bad3)
    check("非法公式 400 定位拒绝", status == 400)

    status, body = http("GET", "/checks/CHK-000000")
    check("不存在编号 404", status == 404)

    # ---- 最小切换抑制审计：两条替代违规环 ----
    section("最小切换抑制审计（两条替代违规环）")
    status, body = http("POST", "/checks", TWO_LOOPS)
    src = body.get("id")
    check("两条替代违规环被判不成立",
          status == 201 and body.get("holds") is False and src,
          f"status={status}")
    before = http("GET", f"/checks/{src}")[1] if src else {}

    status, audit = http("POST", f"/checks/{src}/suppressions")
    sup_id = audit.get("id")
    check("抑制审计 201 且全局最少数量为 2",
          status == 201 and audit.get("min_disabled_count") == 2 and sup_id,
          f"status={status} body={audit}")
    check("禁用切换升序稳定裁决为 ['d1', 'q1']（{t1} 死端被禁选）",
          audit.get("disabled_switches") == ["d1", "q1"],
          f"disabled={audit.get('disabled_switches')}")
    check("审计含来源复核编号与原公式摘要",
          audit.get("source_check_id") == src
          and audit.get("formula_summary", {}).get("formula")
          == TWO_LOOPS["formula"])
    check("修复后结论成立",
          audit.get("post_repair", {}).get("holds") is True)

    status, fetched = http("GET", f"/suppressions/{sup_id}")
    check("审计按编号读取且内容一致",
          status == 200 and fetched.get("id") == sup_id
          and fetched.get("disabled_switches") == ["d1", "q1"],
          f"status={status}")

    reduced = (fetched.get("proof") or {}).get("reduced_procedure")
    status, recheck = http("POST", "/checks", reduced) if reduced else (0, {})
    check("可复算的最终证明：禁用后规程复核成立",
          status == 201 and recheck.get("holds") is True,
          f"status={status}")

    # 原有读取回归：来源复核不被改写，结论仍为不成立、规程原样
    status, after = http("GET", f"/checks/{src}")
    check("原有读取回归：来源复核不被改写",
          status == 200 and after == before
          and after.get("holds") is False
          and after.get("spec", {}).get("switches") == TWO_LOOPS["switches"],
          f"status={status}")

    # 失败定位：来源成立 / 编号不存在 / 无可行修复，均不创建审计
    status, body = http("POST", f"/checks/{ok_id}/suppressions")
    check("来源结论成立 409 且不创建审计",
          status == 409 and body.get("error") == "source_already_holds"
          and "id" not in body,
          f"status={status} body={body}")
    status, body = http("POST", "/checks/CHK-999999/suppressions")
    check("来源编号不存在 404 且不创建审计",
          status == 404 and "id" not in body)
    status, body = http("POST", f"/checks/{starv_id}/suppressions")
    check("无可行修复（保持全部位置可外出）422 且不创建审计",
          status == 422 and body.get("error") == "no_feasible_suppression"
          and "id" not in body,
          f"status={status} body={body}")
    status, body = http("GET", "/suppressions/SUP-999999")
    check("不存在审计编号 404", status == 404)

    section("汇总")
    if FAILURES:
        print(f"verify 失败 {len(FAILURES)} 项：{FAILURES}", flush=True)
        sys.exit(1)
    print("verify 全部通过，退出码 0", flush=True)
    sys.exit(0)


if __name__ == "__main__":
    main()
