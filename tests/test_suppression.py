"""最小切换抑制审计测试。

覆盖：两条替代违规环的全局最少修复、升序稳定裁决、死端约束、
贪心反例（共享切换同时命中两环）、无可行修复、审计持久化（重启可读）、
接口失败定位（来源成立 / 编号不存在 / 无可行修复）与原复核不被改写。
"""

import json
import tempfile
import threading
import unittest
import urllib.error
import urllib.request

from app.checker import check
from app.server import create_server
from app.suppression import NoFeasibleSuppression, minimize_suppression
from app.validation import validate_request

# 两条替代违规环：idle→req→idle（t1,q1 迟发环）与 req→hold→req（d1,d2 悬置环）。
# {t1} 可同时打断两环但会令 idle 失去全部外出切换（禁止）；
# 最少可行修复为 {d1,q1} 与 {d2,q1}，升序裁决取 ["d1","q1"]。
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

# 共享切换反例：s2 同时在两条违规环上，逐条贪心会先禁 s1 再禁 s2（大小 2），
# 分支定界求得全局最少 {s2}（大小 1）。
SHARED_EDGE = {
    "locations": ["z", "a", "b", "c", "grant"],
    "initial": "z",
    "switches": [
        {"id": "t0", "source": "z", "target": "a"},
        {"id": "s2", "source": "a", "target": "b"},
        {"id": "s1", "source": "b", "target": "a"},
        {"id": "s3", "source": "b", "target": "c"},
        {"id": "s4", "source": "c", "target": "a"},
        {"id": "e1", "source": "a", "target": "grant"},
        {"id": "e2", "source": "grant", "target": "a"},
    ],
    "propositions": {
        "z": [], "a": [], "b": ["request"], "c": [], "grant": ["granted"],
    },
    "formula": "G(!request | F granted)",
}

# 永不放行且不可修复：req 的外出只有 t2/t3，禁任一仍留另一违规环，
# 全禁则 req 死端 —— 不存在保持全部位置可外出的修复。
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
        "idle": [], "req": ["request"], "deny": ["denied"],
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


class TestMinimizeSuppression(unittest.TestCase):
    def test_two_alternative_loops_global_minimum(self):
        self.assertFalse(check(validate_request(TWO_LOOPS)).holds)
        out = minimize_suppression(TWO_LOOPS)
        # 全局最少为 2：{t1} 虽同时命中两环但令 idle 死端，禁止
        self.assertEqual(out.disabled, ["d1", "q1"])
        # 修复后规程复核成立（可复算）
        self.assertTrue(
            check(validate_request(out.reduced_payload)).holds
        )
        # 原规程不被改写
        self.assertEqual(len(TWO_LOOPS["switches"]), 7)

    def test_shared_switch_beats_greedy(self):
        out = minimize_suppression(SHARED_EDGE)
        self.assertEqual(out.disabled, ["s2"])
        self.assertTrue(
            check(validate_request(out.reduced_payload)).holds
        )

    def test_no_feasible_repair_raises(self):
        with self.assertRaises(NoFeasibleSuppression):
            minimize_suppression(STARVATION)

    def test_deterministic(self):
        a = minimize_suppression(TWO_LOOPS)
        b = minimize_suppression(TWO_LOOPS)
        self.assertEqual(a.disabled, b.disabled)
        self.assertEqual(a.reduced_payload, b.reduced_payload)

    def test_tie_break_ascending_ids(self):
        # 两条等长可行修复 {d1,q1} 与 {d2,q1}，升序序列取前者
        out = minimize_suppression(TWO_LOOPS)
        self.assertEqual(out.disabled, sorted(out.disabled))
        self.assertLess(["d1", "q1"], ["d2", "q1"])
        self.assertEqual(out.disabled, ["d1", "q1"])


class SuppressionApiTestBase(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self._start_server()

    def _start_server(self):
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

    def url(self, path):
        return f"http://127.0.0.1:{self.port}{path}"

    def request(self, method, path, payload=None):
        data = None
        headers = {}
        if payload is not None:
            data = json.dumps(payload).encode("utf-8")
            headers["Content-Type"] = "application/json"
        req = urllib.request.Request(self.url(path), data=data,
                                     headers=headers, method=method)
        try:
            with urllib.request.urlopen(req, timeout=5) as resp:
                return resp.status, json.loads(resp.read().decode("utf-8"))
        except urllib.error.HTTPError as exc:
            return exc.code, json.loads(exc.read().decode("utf-8"))


class TestSuppressionApi(SuppressionApiTestBase):
    def test_minimal_repair_audit_saved_and_readable(self):
        status, body = self.request("POST", "/checks", TWO_LOOPS)
        self.assertEqual(status, 201)
        self.assertFalse(body["holds"])
        src = body["id"]
        before = self.request("GET", f"/checks/{src}")[1]

        status, audit = self.request("POST", f"/checks/{src}/suppressions")
        self.assertEqual(status, 201)
        self.assertEqual(audit["kind"], "switch_suppression_audit")
        self.assertEqual(audit["source_check_id"], src)
        self.assertEqual(audit["min_disabled_count"], 2)
        self.assertEqual(audit["disabled_switches"], ["d1", "q1"])
        self.assertEqual(
            audit["formula_summary"]["formula"], TWO_LOOPS["formula"]
        )
        self.assertTrue(audit["post_repair"]["holds"])
        self.assertIn("reduced_procedure", audit["proof"])
        self.assertIn("final_check", audit["proof"])

        # 按审计编号读取，内容一致
        status, fetched = self.request("GET", f"/suppressions/{audit['id']}")
        self.assertEqual(status, 200)
        self.assertEqual(fetched, audit)

        # 可复算的最终证明：以禁用后规程重新复核仍成立
        reduced = fetched["proof"]["reduced_procedure"]
        status, recheck = self.request("POST", "/checks", reduced)
        self.assertEqual(status, 201)
        self.assertTrue(recheck["holds"])

        # 原复核与规程不被改写
        after = self.request("GET", f"/checks/{src}")[1]
        self.assertEqual(before, after)
        self.assertFalse(after["holds"])

    def test_source_holds_rejected_no_audit(self):
        status, body = self.request("POST", "/checks", COMPLIANT)
        self.assertTrue(body["holds"])
        ok_id = body["id"]
        status, body = self.request("POST", f"/checks/{ok_id}/suppressions")
        self.assertEqual(status, 409)
        self.assertEqual(body["error"], "source_already_holds")
        self.assertNotIn("id", body)
        # 未创建审计：随后一次成功审计应拿到 SUP-000001
        status, v = self.request("POST", "/checks", TWO_LOOPS)
        status, audit = self.request("POST", f"/checks/{v['id']}/suppressions")
        self.assertEqual(status, 201)
        self.assertEqual(audit["id"], "SUP-000001")

    def test_unknown_check_404(self):
        status, body = self.request("POST", "/checks/CHK-999999/suppressions")
        self.assertEqual(status, 404)
        self.assertNotIn("id", body)

    def test_no_feasible_repair_422_no_audit(self):
        status, body = self.request("POST", "/checks", STARVATION)
        self.assertFalse(body["holds"])
        src = body["id"]
        status, body = self.request("POST", f"/checks/{src}/suppressions")
        self.assertEqual(status, 422)
        self.assertEqual(body["error"], "no_feasible_suppression")
        self.assertNotIn("id", body)
        # 未创建审计：随后一次成功审计仍拿到 SUP-000001
        status, v = self.request("POST", "/checks", TWO_LOOPS)
        status, audit = self.request("POST", f"/checks/{v['id']}/suppressions")
        self.assertEqual(audit["id"], "SUP-000001")

    def test_unknown_suppression_404(self):
        status, _ = self.request("GET", "/suppressions/SUP-999999")
        self.assertEqual(status, 404)

    def test_restart_keeps_audit_readable(self):
        status, body = self.request("POST", "/checks", TWO_LOOPS)
        src = body["id"]
        status, audit = self.request("POST", f"/checks/{src}/suppressions")
        self.assertEqual(status, 201)
        sup_id = audit["id"]

        # 模拟服务重启：同一数据目录重建服务
        self.httpd.shutdown()
        self.httpd.server_close()
        self.thread.join(timeout=5)
        self._start_server()

        status, fetched = self.request("GET", f"/suppressions/{sup_id}")
        self.assertEqual(status, 200)
        self.assertEqual(fetched["id"], sup_id)
        self.assertEqual(fetched["disabled_switches"], ["d1", "q1"])
        self.assertEqual(fetched["source_check_id"], src)
        # 来源复核同样可读
        status, record = self.request("GET", f"/checks/{src}")
        self.assertEqual(status, 200)
        self.assertFalse(record["holds"])


if __name__ == "__main__":
    unittest.main()
