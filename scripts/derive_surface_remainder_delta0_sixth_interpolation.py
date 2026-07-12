"""Independent rational interpolation of the candidate sixth head.

The preceding heads have the structural form ``P(c^2)/c^(3n)``.  We derive
the next coefficient at seven rational ``c`` values, interpolate the degree
six polynomial after multiplying by ``c^18``, then verify two unused exact
points.  This is design output until an immutable target checker reproduces
the resulting closed form symbolically.
"""

import sympy as sp

from derive_surface_remainder_delta0_sixth_candidate import derive_candidate


FIT = tuple(map(sp.Rational, (
    "1", "9/10", "4/5", "3/4", "7/8", "5/6", "11/12")))
CHECK = tuple(map(sp.Rational, ("13/16", "15/16")))


def reconstruct():
    x = sp.symbols("x")
    samples = []
    for c in FIT:
        value = derive_candidate(c)
        samples.append((c**2, sp.factor(value*c**18)))
        print("DESIGN interpolation sample c=%s complete" % c, flush=True)
    polynomial = sp.factor(sp.interpolate(samples, x))
    if sp.degree(polynomial, x) > 6:
        raise AssertionError("candidate exceeds registered structural degree")
    for c in CHECK:
        value = derive_candidate(c)
        if sp.simplify(value*c**18-polynomial.subs(x, c**2)) != 0:
            raise AssertionError("unused-point interpolation check failed")
        print("DESIGN unused check c=%s complete" % c, flush=True)
    return sp.factor(polynomial.subs(x, sp.symbols("c")**2)
                     /sp.symbols("c")**18)


if __name__ == "__main__":
    print("DESIGN interpolated Y delta coefficient 5 =", reconstruct(),
          flush=True)
    print("DESIGN ONLY: immutable symbolic target checker remains open",
          flush=True)
