"""Adjacent finite-G5 design cover for ``25 <= beta <= 30``.

This byte-separate wrapper reuses the audited finite-family judge without
changing the active ``30 <= beta <= 125`` contract.  The three rational
delta bands were fixed only after their adversarial top-lambda cells passed.
Output is design evidence until frozen production and independent rerun.
"""

from fractions import Fraction

import surface_right_edge_five_family_finite_cover_design as base


DELTA_BANDS = (
    (Fraction(1, 30), Fraction(7, 200)),
    (Fraction(7, 200), Fraction(3, 80)),
    (Fraction(3, 80), Fraction(1, 25)),
)

DEPENDENCIES = (
    "scripts/surface_right_edge_five_family_finite_lower_cover_design.py",
    *base.DEPENDENCIES,
)
fraction_string = base.fraction_string


def judge(delta_index, lambda_index):
    return base.judge(delta_index, lambda_index, DELTA_BANDS)


def main():
    return base.main(DELTA_BANDS, DEPENDENCIES)


if __name__ == "__main__":
    raise SystemExit(main())
