"""Design-only cached-Arb acceleration of the compact right-edge lane.

The archived certificate recomputes the same positive power series many
times while forming shifted beta jets.  At exact positive rational beta,
Arb's integer-order ``bessel_i`` is an outward-rounded enclosure.  This
module installs a cache keyed by ``(order,beta)`` and then calls the unchanged
right-edge algebra.  Its terminal marker remains DESIGN until a separate
production script, dependency ledger, transcript validator, and finite target
are frozen in a commit.
"""

import argparse
from fractions import Fraction
from functools import lru_cache
from time import perf_counter

from flint import arb, ctx

import certify_bulk_beta_taylor_arb as bulk
import certify_right_edge_beta_taylor_arb as right


@lru_cache(maxsize=None)
def cached_enc_I(order: int, beta: Fraction):
    if order < 0 or beta <= 0:
        raise ValueError("cached Bessel input outside the positive lane")
    return bulk.aq(beta).bessel_i(order)


def install_cached_backend():
    bulk.enc_I = cached_enc_I


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("beta_lo", type=Fraction)
    parser.add_argument("beta_hi", type=Fraction)
    parser.add_argument("--step", type=Fraction, default=Fraction(1, 10))
    args = parser.parse_args()
    if not args.beta_lo < args.beta_hi:
        parser.error("beta interval must have positive width")
    ctx.prec = 140
    install_cached_backend()
    started = perf_counter()
    boxes, normalized, regular = right.cover_beta(
        args.beta_lo, args.beta_hi, args.step)
    print(
        "RIGHT EDGE CACHED DESIGN PASS",
        args.beta_lo,
        args.beta_hi,
        "beta_boxes",
        boxes,
        "normalized_boxes",
        normalized,
        "regular_boxes",
        regular,
        "cache",
        cached_enc_I.cache_info(),
        "elapsed_seconds",
        perf_counter() - started,
        "PRODUCTION AND HALF-LINE ARGUMENT STILL REQUIRED",
        flush=True,
    )


if __name__ == "__main__":
    main()
