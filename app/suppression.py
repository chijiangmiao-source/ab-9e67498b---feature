"""最小切换抑制审计。

在结论为「不成立」的复核上发起：从**保存的规程与公式**重新构造否定 GBA
乘积，用分支定界求**全局最少**的既有有向切换禁用集，使同一初态起的所有
无限执行都满足原公式。原复核记录与规程只读，绝不改写。

算法（反例引导的必中集分支定界；不是有限回放、不是随机搜索、不是逐条
贪心禁用、也不是仅修补首次证据）：

1. 候选禁用集 D 初始为空；把 D 从规程中移除后跑**完整** LTL 复核
   （否定 GBA × 规程乘积 × 可达接受 SCC，与主复核同一判定核心）。
2. 若成立，D 是一个可行修复；否则取回复核给出的可达接受套索，其
   （前缀 + 闭环）用到的全部切换构成**必中集**：任何可行超集 D* ⊇ D
   必含其中至少一条切换——否则该套索在移除 D* 后仍是一条违规无限
   执行，与 D* 可行矛盾。对必中集逐条分支：D ∪ {sw} 递归复核。
3. 定界与剪枝：候选规模超过当前最优即剪枝；候选令任一位置失去全部
   外出切换（死端）即整枝剪掉（其超集同样不可行）；同一候选集
   （无论由何种顺序到达）只探索一次。
4. 全局最少集合唯一性不保证，但裁决稳定：可行修复先按规模升序，
   同规模再按切换标识的升序序列取最小者；搜索全程确定性（套索切换
   按标识升序分支、判定核心确定性），结果可复算。

终止性：每条切换至多加入候选一次，搜索树深度 ≤ 切换总数，且每个
候选集只访问一次，故必终止；由必中集论证，最优解所在路径上的每个
前缀都不会被剪枝，故返回的必是全局最优（含升序裁决）。
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from .checker import CheckResult, check, push_negation
from .ltl_parser import parse_formula

# 与主复核共用的判定方法说明（可复算证明中注明同一核心）
METHOD = "否定公式广义 Büchi 自动机（tableau）× 规程乘积 × 接受 SCC"


class SpecReconstructionError(Exception):
    """保存的复核记录缺少重建规程所需字段，无法重新构造乘积。"""


def reconstruct_spec(record: Dict[str, Any]) -> Dict[str, Any]:
    """从保存的复核记录重建内部规程结构（只读副本，不改写原记录）。"""
    required = ("locations", "switches", "propositions", "formula", "initial")
    missing = [k for k in required if k not in record]
    if missing:
        raise SpecReconstructionError(
            "复核记录缺少规程字段，无法重构乘积: " + ", ".join(missing)
        )
    locations = list(record["locations"])
    switches = [
        {"id": sw["id"], "source": sw["source"], "target": sw["target"]}
        for sw in record["switches"]
    ]
    propositions = {
        loc: list(plist) for loc, plist in record["propositions"].items()
    }
    declared: Set[str] = set()
    for plist in propositions.values():
        declared.update(plist)
    formula_ast = parse_formula(record["formula"], declared)
    outgoing: Dict[str, List[Dict[str, str]]] = {loc: [] for loc in locations}
    for sw in switches:
        outgoing[sw["source"]].append(sw)
    return {
        "locations": locations,
        "initial": record["initial"],
        "switches": switches,
        "propositions": propositions,
        "formula": record["formula"],
        "formula_ast": formula_ast,
        "outgoing": outgoing,
    }


def _lasso_switch_ids(violation: Dict[str, Any]) -> List[str]:
    """套索（前缀 + 闭环）用到的切换标识，升序去重——本次必中集。"""
    return sorted({step["switch_taken"] for step in violation["steps"]})


def _reduce_spec(
    spec: Dict[str, Any], disabled: FrozenSet[str]
) -> Dict[str, Any]:
    """移除禁用切换后的归约规程（新建结构，原 spec 不被改写）。"""
    remaining = [sw for sw in spec["switches"] if sw["id"] not in disabled]
    outgoing = {
        loc: [sw for sw in spec["outgoing"][loc] if sw["id"] not in disabled]
        for loc in spec["locations"]
    }
    return {**spec, "switches": remaining, "outgoing": outgoing}


@dataclass
class SuppressionSearch:
    """分支定界搜索结果。"""

    disabled: FrozenSet[str]          # 最优禁用集（升序裁决后）
    final: CheckResult                # 归约规程上的最终复核（成立）
    candidates_checked: int           # 实际复核过的候选数
    lassos_examined: int              # 展开过必中集的反例套索数


def find_minimal_suppression(
    spec: Dict[str, Any]
) -> Optional[SuppressionSearch]:
    """求全局最少禁用集；不存在保持全部位置可外出的修复时返回 None。"""
    # 每个位置的外出切换标识集（原规程已通过死端校验，均非空）
    out_ids: Dict[str, FrozenSet[str]] = {
        loc: frozenset(sw["id"] for sw in spec["outgoing"][loc])
        for loc in spec["locations"]
    }

    best: Optional[FrozenSet[str]] = None
    best_key: Optional[Tuple[int, List[str]]] = None
    visited: Set[FrozenSet[str]] = set()
    counters = {"candidates": 0, "lassos": 0}

    def key_of(d: FrozenSet[str]) -> Tuple[int, List[str]]:
        # 裁决键：先规模，再切换标识升序序列
        return (len(d), sorted(d))

    def creates_dead_end(disabled: FrozenSet[str]) -> bool:
        return any(ids <= disabled for ids in out_ids.values())

    def search(disabled: FrozenSet[str]) -> None:
        nonlocal best, best_key
        if disabled in visited:
            return
        visited.add(disabled)
        if best is not None and len(disabled) > len(best):
            return  # 定界：已不可能优于当前最优（同规模仍须探索以裁决）
        if creates_dead_end(disabled):
            return  # 某位置失去全部外出切换；其超集同样不可行
        counters["candidates"] += 1
        result = check(_reduce_spec(spec, disabled))
        if result.holds:
            key = key_of(disabled)
            if best_key is None or key < best_key:
                best, best_key = disabled, key
            return
        counters["lassos"] += 1
        # 必中集分支：任何可行超集必含套索中至少一条切换
        for sw_id in _lasso_switch_ids(result.violation):
            if sw_id not in disabled:
                search(disabled | {sw_id})

    search(frozenset())
    if best is None:
        return None
    # 最终证明：在最优归约规程上复跑一次完整复核（确定性，可复算）
    final = check(_reduce_spec(spec, best))
    return SuppressionSearch(
        disabled=best,
        final=final,
        candidates_checked=counters["candidates"],
        lassos_examined=counters["lassos"],
    )


def build_suppression_record(
    check_record: Dict[str, Any]
) -> Optional[Dict[str, Any]]:
    """在结论不成立的复核记录上构造抑制审计记录；无可行修复返回 None。

    只读取 ``check_record``，绝不改写；返回的记录不含编号（由存储层分配）。
    """
    spec = reconstruct_spec(check_record)
    outcome = find_minimal_suppression(spec)
    if outcome is None:
        return None

    disabled_sorted = sorted(outcome.disabled)
    by_id = {sw["id"]: sw for sw in spec["switches"]}
    neg_nnf = push_negation(spec["formula_ast"], neg=True).to_str()
    final = outcome.final
    return {
        "kind": "switch_suppression_audit",
        "source_check_id": check_record["id"],
        "initial": spec["initial"],
        "formula": spec["formula"],
        "formula_summary": {
            "text": spec["formula"],
            "negation_nnf": neg_nnf,
            "sha256": hashlib.sha256(
                spec["formula"].encode("utf-8")
            ).hexdigest(),
        },
        "min_disabled_count": len(disabled_sorted),
        "disabled_switches": disabled_sorted,
        "disabled_switch_details": [by_id[sw_id] for sw_id in disabled_sorted],
        "holds_after_repair": final.holds,
        "final_proof": {
            "method": METHOD,
            "negation_nnf": neg_nnf,
            "holds": final.holds,
            "violation": final.violation,
            "remaining_switches": [
                sw["id"] for sw in spec["switches"]
                if sw["id"] not in outcome.disabled
            ],
            "stats": final.stats,
            "note": (
                "从保存的规程移除 disabled_switches 后重新构造否定 GBA 乘积"
                "并完整复核，结论为成立；按保存数据可复算出相同结论与统计。"
            ),
        },
        "search": {
            "method": (
                "可达接受套索必中集 + 分支定界（全局最少；同规模按切换标识"
                "升序序列稳定裁决；候选不得令任何位置失去全部外出切换）"
            ),
            "candidates_checked": outcome.candidates_checked,
            "lassos_examined": outcome.lassos_examined,
        },
    }
