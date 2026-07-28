"""Exact symbolic audit of the scaled right-edge zero-face algebra.

This checks coefficient substitution, assembly, hyperbolic simplification,
and the derivative identity.  It deliberately does not certify the uniform
finite-delta remainder.
"""

import sympy as sp
from flint import arb, ctx


def verify():
    lam = sp.symbols("lambda", positive=True)
    r = sp.sqrt(2) / 2
    L = sp.sqrt(2 * sp.pi) * r ** sp.Rational(-5, 2) / 4
    q = sp.exp(-sp.sqrt(2) * lam)

    # The exact next mirror-M_F coefficient printed by the extraction.
    mirror_mf_next = (
        sp.sqrt(2) * sp.sqrt(sp.pi)
        * (46 * r**4 - 23 * r**2 + 4)
        / (32 * r ** sp.Rational(11, 2))
    )
    assert sp.simplify(mirror_mf_next - sp.sqrt(2) * L) == 0

    md0 = 2 * L * (1 - q)
    mf0 = L * (-sp.sqrt(2) + q * (2 * lam + sp.sqrt(2)))
    q0_assembled = sp.cancel(lam / 2 + mf0 / md0)
    q0_closed = lam * sp.coth(lam / sp.sqrt(2)) / 2 - 1 / sp.sqrt(2)
    assert sp.simplify(q0_assembled.rewrite(sp.exp) - q0_closed.rewrite(sp.exp)) == 0

    x = lam / sp.sqrt(2)
    h0 = sp.diff(q0_closed, lam) / lam
    h0_positive_form = (
        sp.sinh(x) * sp.cosh(x) - x
    ) / (2 * lam * sp.sinh(x) ** 2)
    assert sp.simplify(h0 - h0_positive_form) == 0
    assert sp.simplify(
        sp.diff(sp.sinh(x) * sp.cosh(x) - x, lam)
        - sp.sqrt(2) * sp.sinh(x) ** 2
    ) == 0
    # SymPy 1.14's direct two-term hyperbolic limit spuriously returns -oo;
    # audit the removable value from its exact Laurent/Taylor cancellation.
    h0_series = sp.series(h0, lam, 0, 3).removeO()
    assert sp.simplify(h0_series.subs(lam, 0) - 1 / (3 * sp.sqrt(2))) == 0

    # Exact coefficient/induction audit for H0'<0.
    n = sp.symbols("n", integer=True, positive=True)
    coeff_scaled = 8 * n**2 - 6 * n - (9**n - 1) / 4
    assert sp.simplify(coeff_scaled.subs(n, 1)) == 0
    assert sp.simplify(coeff_scaled.subs(n, 2)) == 0
    d_n = 9**n - 1 - (32 * n**2 - 24 * n)
    assert sp.simplify(d_n.subs(n, 3) - 512) == 0
    assert sp.simplify(d_n.subs(n, n + 1) - 9 * d_n
                       - 256 * n * (n - 1)) == 0

    # With monotonicity proved above, one outward-rounded endpoint ball
    # certifies the rational floor H0>1/5 on the complete closed face.
    ctx.prec = 160
    lam_a = arb(3) / 2
    x_a = lam_a / arb(2).sqrt()
    h0_a = (
        x_a.sinh() * x_a.cosh() - x_a
    ) / (2 * lam_a * x_a.sinh() ** 2)
    assert h0_a > arb(1) / 5

    print(
        "SCALED ZERO-FACE ALGEBRA PASS: "
        "Q0=(lambda/2)coth(lambda/sqrt(2))-1/sqrt(2); "
        f"H0>1/5 on [0,3/2] (endpoint {h0_a}); "
        "uniform finite-delta passage remains open"
    )


if __name__ == "__main__":
    verify()
