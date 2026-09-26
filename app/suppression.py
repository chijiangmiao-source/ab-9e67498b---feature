"""最小切换抑制审计（分支定界，全局最少）。

在已判定「不成立」的复核上发起：从保存的规程与公式重新构造否定 GBA 乘积，
每发现一个可达接受套索，就把该套索用到的全部切换（前缀 + 闭环）转为一个
「必须命中」的冲突集 —— 任何可行禁用集都必须至少含其中一个切换，否则该
套索在禁用后的规程中仍然存活（其全部切换都在，乘积路径不变）。分支定界
持续向候选禁用集加入套索内切换并重新复核，直至求得全局最少禁用集合：

- 候选集不得令任一位置失去全部外出切换（保持全部位置可外出）；
- 同样大小的可行修复按切换标识升序序列取字典序最小者（稳定裁决）；
- 不使用有限回放、随机搜索、逐条贪心禁用，也不只修补首次证据：
  每个候选都经完整复核（可达接受 SCC 判定），不可行即按其新套索继续分支。

完备性要点：设 D* 为任一可行禁用集且 D ⊆ D* 已到访。若禁用 D 后仍违规，
所得套索 L 必被 D* 命中（否则 L 在禁用 D* 的规程中存活，矛盾），故某条
分支 D ∪ {s}（s ∈ L ∩ D*）仍 ⊆ D*；归纳可知全部最小可行集都会被到访并
复核，定界只剪掉严格更大的候选，不影响最少性与升序裁决。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from .checker import check
from .validation import validate_request


class NoFeasibleSuppression(Exception):
    """不存在保持全部位置可外出的可行禁用集。"""


@dataclass
class SuppressionOutcome:
    disabled: List[str]               # 全局最少禁用切换（标识升序）
    reduced_payload: Dict[str, Any]   # 禁用后的规程请求体（可复算最终证明）
    candidates_evaluated: int         # 经完整复核的候选禁用集数量
    lassos_eliminated: int            # 被转为冲突集的可达接受套索数量


def _reduced_payload(
    base: Dict[str, Any], disabled: FrozenSet[str]
) -> Dict[str, Any]:
    """由保存的规程构造禁用 ``disabled`` 后的请求体（不改写原规程）。"""
    return {
        "locations": list(base["locations"]),
        "initial": base["initial"],
        "switches": [
            {"id": sw["id"], "source": sw["source"], "target": sw["target"]}
            for sw in base["switches"]
            if sw["id"] not in disabled
        ],
        "propositions": {
            loc: list(props) for loc, props in base["propositions"].items()
        },
        "formula": base["formula"],
    }


def minimize_suppression(base: Dict[str, Any]) -> SuppressionOutcome:
    """求全局最少禁用切换集合；无可行修复抛 :class:`NoFeasibleSuppression`。

    ``base`` 为保存的规程请求体（locations/initial/switches/propositions/
    formula）。返回的禁用列表按标识升序；同样大小的可行修复中本结果为
    升序序列字典序最小者。
    """
    outgoing_ids: Dict[str, List[str]] = {}
    for sw in base["switches"]:
        outgoing_ids.setdefault(sw["source"], []).append(sw["id"])

    best: Optional[Tuple[str, ...]] = None
    visited: Set[FrozenSet[str]] = set()
    candidates = 0
    lassos = 0

    def dead_location(disabled: FrozenSet[str]) -> Optional[str]:
        """disabled 是否令某位置失去全部外出切换（是则返回该位置）。"""
        for loc in sorted(outgoing_ids):
            if all(sid in disabled for sid in outgoing_ids[loc]):
                return loc
        return None

    def solve(disabled: FrozenSet[str]) -> None:
        nonlocal best, candidates, lassos
        if disabled in visited:
            return
        visited.add(disabled)
        if best is not None and len(disabled) > len(best):
            return  # 定界：已不可能更优
        if dead_location(disabled) is not None:
            return  # 保持全部位置可外出：剪枝
        spec = validate_request(_reduced_payload(base, disabled))
        result = check(spec)
        candidates += 1
        if result.holds:
            cand = tuple(sorted(disabled))
            if (
                best is None
                or len(cand) < len(best)
                or (len(cand) == len(best) and cand < best)
            ):
                best = cand
            return
        lassos += 1
        # 可达接受套索 -> 必须命中的切换集合（前缀 + 闭环全部切换）
        conflict = sorted(
            {step["switch_taken"] for step in result.violation["steps"]}
        )
        for sid in conflict:
            if sid not in disabled:
                solve(disabled | {sid})

    solve(frozenset())

    if best is None:
        raise NoFeasibleSuppression(
            "不存在保持全部位置可外出的切换禁用修复：任何不造成死端的禁用集下，"
            "同一初态仍存在违反原公式的无限执行"
        )
    return SuppressionOutcome(
        disabled=list(best),
        reduced_payload=_reduced_payload(base, frozenset(best)),
        candidates_evaluated=candidates,
        lassos_eliminated=lassos,
    )
