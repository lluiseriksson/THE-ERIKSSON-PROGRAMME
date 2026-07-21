"""Non-rigorous cancellation diagnostic for the remaining scaled bulk seam.

This does not certify a sign.  It samples finite scaled Fourier sums at exact
rational beta points and reports the cancellation index
`kappa = 2(|A_t||B|+|A||B_t|)/|W|`, where
`W=2(A_t B-A B_t)`.  It is a routing diagnostic for the grouped backend.
"""

from fractions import Fraction
from functools import lru_cache
from math import pi

from flint import arb, ctx

import certify_bulk_beta_taylor_scaled_design as scaled


@lru_cache(maxsize=None)
def coefficient_arrays(beta, M):
    j = {n: scaled.scaled_bessel_value(n, beta)
         for n in range(0, M+3)}
    a, b = {}, {}
    for m in range(1, M+2):
        a[m] = j[m]**2*((m-1)*j[m-1]**2+(m+1)*j[m+1]**2)
        b[m] = arb(m)*j[m]**4
    return a, b


def sample(beta, t, M):
    a, b = coefficient_arrays(beta, M)
    af = at = bf = bt = arb(0)
    # The first version fed binary64 sin/cos values into Arb.  That creates a
    # 53-bit angular noise floor precisely in the regime this diagnostic is
    # meant to inspect.  Evaluate the trigonometric factors in Arb at the
    # active precision instead; this remains a diagnostic, but no longer has
    # an avoidable low-precision input channel.
    T = arb(str(t))
    for m in range(1, M+1):
        mt = arb(m)*T
        sm, cm = mt.sin(), mt.cos()
        af += a[m]*sm; at += arb(m)*a[m]*cm
        bf += b[m]*sm; bt += arb(m)*b[m]*cm
    w = 2*(at*bf-af*bt)
    scale = 2*(abs(float(at))*abs(float(bf))
               + abs(float(af))*abs(float(bt)))
    value = abs(float(w))
    return float(w), scale/value if value else float("inf"), t


def main():
    ctx.prec = 180
    best = None
    worst_kappa = None
    positive = negative = 0
    for bi in range(0, 25):
        beta = Fraction(1629, 16) + Fraction(bi, 16)
        beta_f = float(beta)
        M = int(beta)+55
        t_hi = pi-4/beta_f
        local_min = None
        for ti in range(121):
            t = 0.6+(t_hi-0.6)*ti/120
            signed, kappa, arg = sample(beta, t, M)
            value = abs(signed)
            positive += signed > 0
            negative += signed < 0
            if local_min is None or value < local_min[0]:
                local_min = (value, kappa, arg, signed)
            if worst_kappa is None or kappa > worst_kappa[0]:
                worst_kappa = (kappa, beta_f, t, value)
        if best is None or local_min[0] < best[0]:
            best = (local_min[0], beta_f, local_min[1], local_min[2])
        print("BETA", beta, "min_abs_W", local_min[0],
              "signed_at_min", local_min[3], "kappa_at_min", local_min[1],
              "t", local_min[2], flush=True)
    print("CANCELLATION DIAGNOSTIC ONLY")
    print("GLOBAL_MIN", best)
    print("GLOBAL_MAX_KAPPA", worst_kappa)
    print("SIGN_COUNTS", "positive", positive, "negative", negative)


if __name__ == "__main__":
    main()
