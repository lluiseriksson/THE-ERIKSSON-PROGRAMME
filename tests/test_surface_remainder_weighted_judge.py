from __future__ import annotations

import sys
from pathlib import Path

from flint import arb


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import surface_remainder_weighted_judge_design as judge  # noqa: E402


def test_literal_weight_integrates_endpoint_kernel() -> None:
    delta = arb(1) / 15
    partition = [arb(0), delta / 3, 2 * delta / 3, delta]
    total = sum(
        judge.taylor_weight(lo, hi)
        for lo, hi in zip(partition, partition[1:])
    )
    assert total.overlaps(delta**2 / 2)


def test_zero_profile_passes_all_seven_budget_rows() -> None:
    delta = arb(1) / 15
    rows = judge.judge_rows(
        [arb(0), delta], [{name: arb(0) for name in judge.NAMES}]
    )
    assert len(rows) == 7
    assert all(passed for _, _, passed in rows.values())


def test_adaptive_integrator_preserves_constant_cell_integral() -> None:
    names = judge.NAMES

    def evaluator(slo, shi, alo, ahi):
        area = (shi - slo) * (ahi - alo)
        return {name: area for name in names}

    totals = judge._adaptive_integral(
        [(arb(0), arb(1), arb(0), arb(1))], evaluator, 16
    )
    assert all(value.overlaps(arb(1)) for value in totals.values())
