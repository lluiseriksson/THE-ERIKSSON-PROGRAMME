"""Cross-check the adversarial row-63 Arb box against the Fourier oracle.

This is a regression/audit, not a substitute for the interval proof.  It
requires the five family values and the assembled P0,H at beta=125 to lie
inside the single Arb enclosure for lambda in [63/50,64/50].
"""

import mpmath as mp
from flint import arb, ctx

import surface_right_edge_divided_difference_truth_map as truth
import surface_right_edge_five_family_cover_design as cover


def aq(value):
    return arb(mp.nstr(value, 100))


def verify():
    ctx.prec = 160
    budgets = cover.family_tail_budgets()
    resolution, families, p0_box, h_box = cover.judge(63, budgets)
    assert resolution == "coarse"
    beta = mp.mpf(125)
    mp.mp.dps = 220
    values = truth.scaled_bessel_row(beta, 220)
    for lam_text in ("1.26", "1.27", "1.28"):
        row = truth.target(beta, mp.mpf(lam_text), values)
        for enclosure, point in zip(families, row[:5]):
            assert enclosure.contains(aq(point))
        assert p0_box.contains(aq(row[5]))
        assert h_box.contains(aq(row[6]))
        assert aq(row[6]) > arb(h_box.lower())
    return arb(h_box.lower())


def main():
    lower = verify()
    print("RIGHT-EDGE FIVE-FAMILY ORACLE CROSS-CHECK PASS row 63 "
          "beta 125 lambdas 1.26,1.27,1.28 H_lower", lower)


if __name__ == "__main__":
    main()
