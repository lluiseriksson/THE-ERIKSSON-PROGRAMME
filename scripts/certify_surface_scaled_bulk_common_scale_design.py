"""Design-only common positive scaling for one finite-beta bridge box.

The scale is fixed at the beta-box midpoint and is independent of beta and t,
so it rescales the exact Wronskian by a positive constant.  Every derivative
and absolute tail accumulator is scaled after construction; no mathematical
formula or stopping rule is changed.
"""

from fractions import Fraction

import certify_bulk_beta_taylor_scaled_sign_rows_cwin3p2_high as high


RAW_BOX = high.scaled.bulk.BetaTaylorBox


def _scale_nested(values, factor):
    return [tuple(item * factor for item in row) for row in values]


class CommonScaleBox(RAW_BOX):
    def __init__(self, beta_lo, beta_hi, *args, **kwargs):
        super().__init__(beta_lo, beta_hi, *args, **kwargs)
        j1 = high.scaled.scaled_bessel_value(1, self.beta_mid)
        s0 = j1**4
        assert s0.lower() > 0, s0
        factor = 1 / s0
        self.common_scale = s0
        for table in (self.aj, self.bj):
            for index, row in enumerate(table):
                table[index] = [value * factor for value in row]
        for table in (self.ac, self.bc):
            for index, value in enumerate(table):
                table[index] = value * factor
        self.center_tails_by_order = [
            tuple(value * factor for value in row)
            for row in self.center_tails_by_order
        ]
        self.abs_center = [
            [tuple(value * factor for value in row) for row in order_row]
            for order_row in self.abs_center
        ]
        self.abs_sums = [
            tuple(value * factor for value in row) for row in self.abs_sums
        ]


def install():
    high.scaled.bulk.BetaTaylorBox = CommonScaleBox


def main() -> int:
    install()
    high.CWIN = Fraction(3, 2)
    high.ORDER = 30
    high.T_ORDER = 37
    high.PREC = 180
    high.MIN_DT = Fraction(1, 100_000)
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--unit", required=True)
    parser.add_argument("--lo", required=True)
    parser.add_argument("--hi", required=True)
    args = parser.parse_args()
    print(high.run(args.unit, Fraction(args.lo), Fraction(args.hi)), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
