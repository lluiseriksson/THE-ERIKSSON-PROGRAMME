"""Diagnostic-only direct/pairwise comparison for the scaled bulk seam.

The pair form removes the identically cancelling diagonal terms in
``A_t B-A B_t``.  It is deliberately not a certificate: no tail enclosure or
cell cover is claimed here.  The script is used to decide whether a future
Arb/Taylor backend should be grouped before interval evaluation.
"""

from fractions import Fraction
from math import pi

from flint import arb, ctx

import probe_surface_scaled_bulk_cancellation as direct


def pair_sample(beta, t, M):
    a, b = direct.coefficient_arrays(beta, M)
    T = arb(str(t))
    total = arb(0)
    for m in range(1, M + 1):
        sm = (arb(m) * T).sin()
        cm = (arb(m) * T).cos()
        for n in range(m + 1, M + 1):
            sn = (arb(n) * T).sin()
            cn = (arb(n) * T).cos()
            kernel = arb(m) * cm * sn - arb(n) * sm * cn
            total += (a[m] * b[n] - a[n] * b[m]) * kernel
    return 2 * total


def main():
    beta_values = [Fraction(1629, 16), Fraction(1633, 16), Fraction(103)]
    for precision in (100, 180, 260):
        ctx.prec = precision
        direct.coefficient_arrays.cache_clear()
        print("PRECISION", precision)
        for beta in beta_values:
            beta_f = float(beta)
            M = int(beta) + 55
            t_hi = pi - 4 / beta_f
            points = (0.8, 1.5, 2.2, 2.8, t_hi - 0.01)
            for t in points:
                w_direct, _, _ = direct.sample(beta, t, M)
                w_pair = pair_sample(beta, t, M)
                print("BETA", beta, "T", repr(t),
                      "DIRECT", w_direct,
                      "PAIR", float(w_pair),
                      "SIGNS", (w_direct > 0), (w_pair > 0))
    print("PAIR SANITY DIAGNOSTIC ONLY; NO G2/G6 PROMOTION")


if __name__ == "__main__":
    main()
