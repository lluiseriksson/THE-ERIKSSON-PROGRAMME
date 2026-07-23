"""High-order point probe at the quarantined unit-82 boundary.

This deliberately evaluates the normalized sign quantity ``W^J`` at exact
beta/t points.  It is a falsification/diagnostic tool only: it cannot imply
the absolute ``H_tail`` relay or promote G2/G6.
"""

from fractions import Fraction
from functools import lru_cache

from flint import ctx

import certify_bulk_beta_taylor_scaled_design as scaled


POINT_T = Fraction("3.1178733989897687")
BETAS = (Fraction(275, 4), Fraction(551, 8), Fraction(69))


def main() -> None:
    ctx.prec = 220
    original = scaled.scaled_bessel_value

    @lru_cache(maxsize=None)
    def cached(mode, beta):
        return original(mode, beta)

    scaled.scaled_bessel_value = cached
    scaled.install_design_backend()
    scaled.bulk.CWIN = Fraction(3, 2)
    print("UNIT82 POINT PROBE W^J")
    print("config beta_order 30 t_order 35 prec 220")
    print("point_t", POINT_T)
    for beta in BETAS:
        half_width = Fraction(1, 10**12)
        box = scaled.bulk.BetaTaylorBox(beta-half_width, beta+half_width, prec=220,
                                        order=30, t_order=35)
        value = box.W(POINT_T, POINT_T)
        print("beta", beta, "WJ", value.str(100))
    print("DESIGN ONLY; NO H_tail/G2/G6 PROMOTION")


if __name__ == "__main__":
    main()
