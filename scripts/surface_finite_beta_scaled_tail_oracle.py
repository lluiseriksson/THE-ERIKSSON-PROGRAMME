"""Finite-sum audit of the scaled Fourier derivative-tail majorant.

This checks the registered factor ``8(1+2(m+1)/beta_lo)`` against direct
scaled coefficient jets on a high-beta stress tail.  It is a contract
regression, not an exhaustive beta/t certificate.
"""

from fractions import Fraction

from flint import arb, ctx

import certify_bulk_beta_taylor_arb as raw
import certify_bulk_beta_taylor_scaled_design as scaled


def main():
    ctx.prec = 180
    beta_lo, beta_hi = Fraction(20), Fraction(201, 10)
    k = int(beta_hi) + 56
    I = [raw.enc_I(m, beta_lo) for m in range(k + 4)]
    a, b, _, _ = raw.coefficient_arrays(I, k - 1)
    r = raw.coefficient_tail_ratio(raw.aq(beta_hi), k)
    print("SCALED FOURIER TAIL ORACLE", "beta", beta_lo, beta_hi,
          "k", k, "ratio", r, flush=True)
    for family, source in (("a", a), ("b", b)):
        for q in range(5):
            bound = scaled.scaled_general_derivative_tail(
                source[k], k, r, beta_lo, q)
            direct = arb(0)
            for m in range(k, k + 12):
                jets = scaled.scaled_coefficient_jets(m, beta_lo, 4)
                value = jets[0][q] if family == "a" else jets[1][q]
                direct += arb(abs(value.upper()))
            if not bound > direct:
                raise SystemExit(("tail majorant failed", family, q,
                                  bound, direct))
            print("ROW", family, q, "direct", direct.str(12),
                  "majorant", bound.str(12), flush=True)
    print("SCALED FOURIER TAIL ORACLE PASS; FINITE-SUM CHECK ONLY")


if __name__ == "__main__":
    main()
