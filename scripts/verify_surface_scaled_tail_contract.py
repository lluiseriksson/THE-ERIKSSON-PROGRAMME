"""Executable audit of the finite-beta scaled Fourier-tail contract.

This checks the frozen geometric ratios and compares the factor-8 derivative
majorant with direct finite scaled sums.  It is a contract audit, not a
coverage certificate by itself.
"""

from fractions import Fraction

from flint import arb, ctx

import certify_bulk_beta_taylor_scaled_design as scaled


def check_box(beta_lo, beta_hi):
    ctx.prec = 180
    xhi = arb(beta_hi.numerator)/arb(beta_hi.denominator)
    blo = arb(beta_lo.numerator)/arb(beta_lo.denominator)
    m0 = int(beta_hi) + 55 + 1
    q = xhi/(2*arb(m0+1))
    qprev = xhi/(2*arb(m0))
    rb = arb(m0+1)/arb(m0)*q**4
    ra = q**2*qprev**2*(arb(m0)+(m0+2)*q**2)/(m0-1)
    assert rb < arb(1)/2 and ra < arb(1)/2
    for m in range(m0, m0+12):
        qm = xhi/(2*arb(m+1))
        qpm = xhi/(2*arb(m))
        rbm = arb(m+1)/arb(m)*qm**4
        ram = qm**2*qpm**2*(arb(m)+(m+2)*qm**2)/(m-1)
        assert rbm.upper() <= rb.upper() and ram.upper() <= ra.upper()

    # Direct finite sums are positive and use the same exact scaled jets as
    # production.  The majorant must dominate every tested order/weight.
    for family in ("a", "b"):
        for order in range(5):
            for weight in (0, 1, 2):
                k = m0
                jets = []
                for m in range(k, k+12):
                    a, b = scaled.scaled_coefficient_jets(
                        m, beta_lo, order)
                    jets.append((a if family == "a" else b)[order].abs_upper())
                direct = sum((arb(k+j)**weight*arb(v)
                              for j, v in enumerate(jets)), arb(0))
                source = scaled.scaled_coefficient_jets(
                    k, beta_lo, order)[0 if family == "a" else 1][0]
                ratio = ra if family == "a" else rb
                major = scaled.scaled_general_derivative_tail(
                    source, k, ratio, beta_lo, order, weight)
                assert direct <= major
    return rb, ra


def main():
    for lo, hi in ((Fraction(20), Fraction(201, 10)),
                   (Fraction(40), Fraction(401, 10)),
                   (Fraction(80), Fraction(801, 10)),
                   (Fraction(111), Fraction(1000, 9))):
        rb, ra = check_box(lo, hi)
        print("TAIL CONTRACT BOX", lo, hi,
              "r_b", rb.str(12), "r_a", ra.str(12), flush=True)
    print("SURFACE SCALED TAIL CONTRACT PASS; AUDIT ONLY")


if __name__ == "__main__":
    main()
