"""最小切换抑制审计测试：

- 分支定界求全局最少禁用集（两条替代违规环、共享干路、多解升序裁决）；
- 候选不得令任何位置失去全部外出切换；
- 原复核与规程不被改写；
- 失败定位：来源成立 409、编号不存在 404、无可行修复 422，均不创建审计；
- 审计按编号持久化，服务重启后仍可读取。
"""

import json
import tempfile
import threading
import unittest
import urllib.error
import urllib.request

from app.checker import check
from app.server import create_server
from app.suppression import (
    find_minimal_suppression,
    reconstruct_spec,
)
from app.validation import validate_request

# 两条替代违规环：req->wait_a->req 与 req->wait_b->req 均永不放行；
# 每条环两条边都可破（a1/a2、b1/b2），共 4 个同尺寸可行修复，
# 升序裁决必须返回 [a1, b1]。
TWO_LOOPS = {
    "locations": ["idle", "req", "wait_a", "wait_b", "grant"],
    "initial": "idle",
    "switches": [
        {"id": "t1", "source": "idle", "target": "req"},
        {"id": "a1", "source": "req", "target": "wait_a"},
        {"id": "a2", "source": "wait_a", "target": "req"},
        {"id": "a3", "source": "wait_a", "target": "grant"},
        {"id": "b1", "source": "req", "target": "wait_b"},
        {"id": "b2", "source": "wait_b", "target": "req"},
        {"id": "b3", "source": "wait_b", "target": "grant"},
        {"id": "g1", "source": "req", "target": "grant"},
        {"id": "g2", "source": "grant", "target": "idle"},
    ],
    "propositions": {
        "idle": [],
        "req": ["request"],
        "wait_a": ["request"],
        "wait_b": ["request"],
        "grant": ["granted"],
    },
    "formula": "G(!request | F granted)",
}

# 共享干路：两条违规环都必经 t1；idle 有自环 t0，故禁用 t1 不造死端，
# 全局最少为 1 条（逐条贪心或仅修首次证据都无法给出更优解）。
SHARED_STEM = {
    "locations": ["idle", "req", "loop_a", "loop_b", "grant"],
    "initial": "idle",
    "switches": [
        {"id": "t0", "source": "idle", "target": "idle"},
        {"id": "t1", "source": "idle", "target": "req"},
        {"id": "t2", "source": "req", "target": "loop_a"},
        {"id": "t3", "source": "loop_a", "target": "req"},
        {"id": "t4", "source": "req", "target": "loop_b"},
        {"id": "t5", "source": "loop_b", "target": "req"},
        {"id": "t6", "source": "req", "target": "grant"},
        {"id": "t7", "source": "grant", "target": "idle"},
    ],
    "propositions": {
        "idle": [],
        "req": ["request"],
        "loop_a": ["request"],
        "loop_b": ["request"],
        "grant": ["granted"],
    },
    "formula": "G(!request | F granted)",
}

# 无可行修复：破两条环必然令 idle/req/deny 之一失去全部外出切换。
NO_REPAIR = {
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


def spec(payload):
    return validate_request(payload)


class TestMinimalSuppression(unittest.TestCase):
    def test_two_alternative_loops_global_minimum(self):
        s = spec(TWO_LOOPS)
        self.assertFalse(check(s).holds)
        out = find_minimal_suppression(s)
        self.assertIsNotNone(out)
        # 全局最少 2 条；4 个同尺寸可行修复中按标识升序序列取 [a1, b1]
        self.assertEqual(sorted(out.disabled), ["a1", "b1"])
        self.assertTrue(out.final.holds)
        self.assertIsNone(out.final.violation)

    def test_shared_stem_single_switch_suffices(self):
        s = spec(SHARED_STEM)
        self.assertFalse(check(s).holds)
        out = find_minimal_suppression(s)
        self.assertIsNotNone(out)
        self.assertEqual(sorted(out.disabled), ["t1"])
        self.assertTrue(out.final.holds)

    def test_no_feasible_repair_returns_none(self):
        s = spec(NO_REPAIR)
        self.assertFalse(check(s).holds)
        self.assertIsNone(find_minimal_suppression(s))

    def test_candidate_never_creates_dead_end(self):
        # 解中禁用任一位置的最后一条外出切换都是非法的；
        # TWO_LOOPS 中 wait_a/wait_b 仅剩一条回路时不得被选
        s = spec(TWO_LOOPS)
        out = find_minimal_suppression(s)
        remaining = {
            loc: [sw for sw in s["outgoing"][loc]
                  if sw["id"] not in out.disabled]
            for loc in s["locations"]
        }
        for loc, outs in remaining.items():
            self.assertTrue(outs, f"位置 {loc} 失去全部外出切换")

    def test_original_spec_not_modified(self):
        s = spec(TWO_LOOPS)
        before = json.dumps(
            {"switches": s["switches"],
             "outgoing": {k: v for k, v in s["outgoing"].items()}},
            sort_keys=True, default=str)
        find_minimal_suppression(s)
        after = json.dumps(
            {"switches": s["switches"],
             "outgoing": {k: v for k, v in s["outgoing"].items()}},
            sort_keys=True, default=str)
        self.assertEqual(before, after)

    def test_reconstruct_spec_from_saved_record(self):
        s = spec(TWO_LOOPS)
        record = {
            "id": "CHK-000001",
            "formula": s["formula"],
            "initial": s["initial"],
            "locations": s["locations"],
            "switches": s["switches"],
            "propositions": s["propositions"],
        }
        rebuilt = reconstruct_spec(record)
        self.assertEqual(rebuilt["formula_ast"].to_str(),
                         s["formula_ast"].to_str())
        self.assertEqual(rebuilt["outgoing"], s["outgoing"])
        # 缺字段的记录必须定位失败
        with self.assertRaises(Exception):
            reconstruct_spec({"id": "CHK-000002", "formula": "G p"})


class SuppressionApiTestBase(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.httpd = create_server("127.0.0.1", 0, self.tmp.name)
        self.port = self.httpd.server_address[1]
        self.thread = threading.Thread(target=self.httpd.serve_forever,
                                       daemon=True)
        self.thread.start()

    def tearDown(self):
        self.httpd.shutdown()
        self.httpd.server_close()
        self.thread.join(timeout=5)
        self.tmp.cleanup()

    def request(self, method, path, payload=None):
        data = None
        headers = {}
        if payload is not None:
            data = json.dumps(payload).encode("utf-8")
            headers["Content-Type"] = "application/json"
        url = f"http://127.0.0.1:{self.port}{path}"
        req = urllib.request.Request(url, data=data, headers=headers,
                                     method=method)
        try:
            with urllib.request.urlopen(req, timeout=5) as resp:
                return resp.status, json.loads(resp.read().decode("utf-8"))
        except urllib.error.HTTPError as exc:
            return exc.code, json.loads(exc.read().decode("utf-8"))


class TestSuppressionApi(SuppressionApiTestBase):
    def test_create_and_read_audit(self):
        status, chk = self.request("POST", "/checks", TWO_LOOPS)
        self.assertEqual(status, 201)
        self.assertFalse(chk["holds"])
        chk_id = chk["id"]

        status, audit = self.request(
            "POST", f"/checks/{chk_id}/suppression-audits")
        self.assertEqual(status, 201)
        self.assertTrue(audit["id"].startswith("SUP-"))
        self.assertEqual(audit["source_check_id"], chk_id)
        self.assertEqual(audit["min_disabled_count"], 2)
        self.assertEqual(audit["disabled_switches"], ["a1", "b1"])
        self.assertTrue(audit["holds_after_repair"])
        # 原公式摘要与可复算最终证明
        self.assertEqual(audit["formula_summary"]["text"],
                         TWO_LOOPS["formula"])
        self.assertIn("negation_nnf", audit["formula_summary"])
        proof = audit["final_proof"]
        self.assertTrue(proof["holds"])
        self.assertIn("stats", proof)
        self.assertNotIn("a1", proof["remaining_switches"])
        self.assertNotIn("b1", proof["remaining_switches"])

        # 按审计编号读取（刷新后仍可读取）
        status, fetched = self.request(
            "GET", f"/suppression-audits/{audit['id']}")
        self.assertEqual(status, 200)
        self.assertEqual(fetched["id"], audit["id"])
        self.assertEqual(fetched["disabled_switches"], ["a1", "b1"])
        self.assertEqual(fetched["source_check_id"], chk_id)

        # 原复核与规程不被改写
        status, orig = self.request("GET", f"/checks/{chk_id}")
        self.assertEqual(status, 200)
        self.assertFalse(orig["holds"])
        self.assertIsNotNone(orig["violation"])
        self.assertEqual(len(orig["switches"]), len(TWO_LOOPS["switches"]))

    def test_audit_survives_restart(self):
        status, chk = self.request("POST", "/checks", TWO_LOOPS)
        status, audit = self.request(
            "POST", f"/checks/{chk['id']}/suppression-audits")
        self.assertEqual(status, 201)
        sup_id = audit["id"]
        # 模拟服务重启：同一数据目录另起服务
        self.httpd.shutdown()
        self.httpd.server_close()
        self.thread.join(timeout=5)
        self.httpd = create_server("127.0.0.1", 0, self.tmp.name)
        self.port = self.httpd.server_address[1]
        self.thread = threading.Thread(target=self.httpd.serve_forever,
                                       daemon=True)
        self.thread.start()
        status, fetched = self.request("GET", f"/suppression-audits/{sup_id}")
        self.assertEqual(status, 200)
        self.assertEqual(fetched["id"], sup_id)
        self.assertEqual(fetched["disabled_switches"], ["a1", "b1"])
        self.assertEqual(fetched["min_disabled_count"], 2)

    def test_source_holds_rejected_409(self):
        status, chk = self.request("POST", "/checks", COMPLIANT)
        self.assertTrue(chk["holds"])
        status, body = self.request(
            "POST", f"/checks/{chk['id']}/suppression-audits")
        self.assertEqual(status, 409)
        self.assertEqual(body["error"], "source_holds")
        self.assertNotIn("id", body)
        # 不创建审计
        status, _ = self.request("GET", "/suppression-audits/SUP-000001")
        self.assertEqual(status, 404)

    def test_unknown_check_404(self):
        status, body = self.request(
            "POST", "/checks/CHK-999999/suppression-audits")
        self.assertEqual(status, 404)
        self.assertNotIn("id", body)

    def test_no_feasible_repair_422(self):
        status, chk = self.request("POST", "/checks", NO_REPAIR)
        self.assertEqual(status, 201)
        self.assertFalse(chk["holds"])
        status, body = self.request(
            "POST", f"/checks/{chk['id']}/suppression-audits")
        self.assertEqual(status, 422)
        self.assertEqual(body["error"], "no_feasible_suppression")
        self.assertNotIn("id", body)
        status, _ = self.request("GET", "/suppression-audits/SUP-000001")
        self.assertEqual(status, 404)

    def test_unknown_audit_id_404(self):
        status, _ = self.request("GET", "/suppression-audits/SUP-999999")
        self.assertEqual(status, 404)

    def test_check_record_carries_spec_for_reconstruction(self):
        status, chk = self.request("POST", "/checks", TWO_LOOPS)
        self.assertEqual(status, 201)
        for key in ("locations", "switches", "propositions",
                    "formula", "initial"):
            self.assertIn(key, chk)


if __name__ == "__main__":
    unittest.main()
