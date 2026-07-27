"""Verify that the certified K2 main carrier is nonnegative.

K2 gives

    |X_main - T*delta - r2*delta^2| <= Theta3*delta^3.

For delta>0 it is therefore enough to certify

    T + r2*delta - Theta3*delta^2 > 0.

The check deliberately covers the larger rectangle
``delta in [0,9/1000], t in [0,pi]``.  It only promotes ``X_main`` on
the subset where the K2 certificate itself applies.
"""

from __future__ import annotations

from fractions import Fraction

from flint import arb, ctx

try:
    from scripts.surface_remainder_arb_jet2 import hull
    from scripts.surface_remainder_delta0_series_cover_design import (
        aq,
        born_t_boxes,
    )
    from scripts.surface_remainder_s2_direct_judge import closed_forms
except ModuleNotFoundError:
    from surface_remainder_arb_jet2 import hull
    from surface_remainder_delta0_series_cover_design import aq, born_t_boxes
    from surface_remainder_s2_direct_judge import closed_forms


DELTA_MAX = Fraction(9, 1000)


def verify() -> dict[str, object]:
    ctx.prec = 140
    delta = hull(arb(0), aq(DELTA_MAX))
    worst = None
    count = 0
    for index, (lo, hi) in enumerate(born_t_boxes()):
        t = hull(aq(lo), aq(hi))
        leading, r2, _, theta3 = closed_forms(t)
        bracket = leading + r2 * delta - theta3 * aq(DELTA_MAX) ** 2
        lower = arb(bracket.lower())
        if not lower > 0:
            raise AssertionError(
                f"K2 main positivity unresolved on t-box {lo}:{hi}: {bracket}"
            )
        if worst is None or lower < worst[0]:
            worst = (lower, index, lo, hi, bracket)
        count += 1
    return {
        "passed": True,
        "boxes": count,
        "worst_lower": worst[0],
        "worst_index": worst[1],
        "worst_lo": worst[2],
        "worst_hi": worst[3],
        "worst_ball": worst[4],
    }


def main() -> int:
    result = verify()
    print(
        "K2 MAIN POSITIVITY PASS",
        f"boxes={result['boxes']}",
        f"worst_index={result['worst_index']}",
        f"t={result['worst_lo']}:{result['worst_hi']}",
        f"lower={result['worst_lower'].str(30)}",
    )
    print(
        "IMPLICATION: on the certified K2 domain, delta>0 => X_main>0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
