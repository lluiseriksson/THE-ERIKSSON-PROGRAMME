"""Single-box conditioning probe for the registered post-102 design."""

from __future__ import annotations

import argparse
from fractions import Fraction
from functools import lru_cache

from flint import ctx
import certify_bulk_beta_taylor_scaled_design as scaled

CWIN = Fraction(3, 2)
ORDER = 22
T_ORDER = 25
PREC = 180
MIN_DT = Fraction(1, 100_000)


def install_cached_backend():
    original = scaled.scaled_bessel_value

    @lru_cache(maxsize=None)
    def cached(mode, beta):
        return original(mode, beta)

    scaled.scaled_bessel_value = cached
    scaled.install_design_backend()
    scaled.bulk.CWIN = CWIN
    return cached


def cover_rows(box, t_lo, t_hi):
    stack, rows = [(t_lo, t_hi)], []
    while stack:
        left, right = stack.pop()
        upper = box.W(left, right).upper()
        if upper < 0:
            rows.append((left, right, upper))
            continue
        if right - left <= MIN_DT:
            raise RuntimeError(f"failure near t={float(left)}")
        middle = (left + right) / 2
        stack.extend(((middle, right), (left, middle)))
    return sorted(rows, key=lambda row: row[0])


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--lo", required=True)
    parser.add_argument("--hi", required=True)
    args = parser.parse_args()
    lo, hi = Fraction(args.lo), Fraction(args.hi)
    ctx.prec = PREC
    cache = install_cached_backend()
    box = scaled.bulk.BetaTaylorBox(lo, hi, prec=PREC, order=ORDER,
                                    t_order=T_ORDER)
    rows = cover_rows(box, Fraction(3, 5), scaled.bulk.PI_UP - CWIN / hi)
    print("POST102 ORDER22 DESIGN PASS", "beta", lo, hi,
          "rows", len(rows), "cache", cache.cache_info().currsize)
    print("DIAGNOSTIC ONLY; NO PRODUCTION/REPLAY OR G2/G6 PROMOTION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
