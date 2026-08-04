"""Exact arithmetic audit for the proposed normalized G2 head.

This checks only algebraic coefficient signs and conservative coefficient-sum
bounds.  It deliberately carries no interval tail or theorem load.
"""

from fractions import Fraction as F


def poly(coeffs, u):
    return sum(F(a)*u**k for k, a in enumerate(coeffs))


def main():
    us = [F(1, 2) + F(k, 200) for k in range(101)]
    # T=(4u-1)/(8u^(3/2)); its minimum is the endpoint value sqrt(2)/4.
    assert min(4*u-1 for u in us) == F(1)
    # r2 and r3 numerators from the manuscript.
    r2 = [-4, 15, -8]
    r3 = [-224, 796, -485, -12]
    assert min(poly(r2, u) for u in us) > 0
    assert min(poly(r3, u) for u in us) > 0

    # Newly derived candidates, represented as polynomials in u=c^2.
    r7 = [-513015808, 2254849024, -2880628992, 1046587520,
          -52644752, 11636676, 6775103, 2085412]
    r8 = [-33064504, 153352416, -219463616, 104539328,
          -12653880, 637408, 323054, 119595, 19936]
    # Denominator floors c^21 >= (1/2)^(21/2) > 1/2048 and
    # c^24 >= (1/2)^12 = 1/4096.  The resulting rational bounds are
    # intentionally coarse and are only a reproducibility check.
    r7_bound = sum(abs(F(a)) for a in r7) * 2048 / F(33554432)
    r8_bound = sum(abs(F(a)) for a in r8) * 4096 / F(524288)
    assert r7_bound < F(500000)
    assert r8_bound < F(5000000)
    print("G2 NORMALIZED HEAD AUDIT PASS; DESIGN ONLY")
    print("r2_min_numerator", min(poly(r2, u) for u in us))
    print("r3_min_numerator", min(poly(r3, u) for u in us))
    print("r7_coarse_bound", float(r7_bound))
    print("r8_coarse_bound", float(r8_bound))


if __name__ == "__main__":
    main()
