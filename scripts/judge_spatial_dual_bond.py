"""Symbolic gate for one theorem: the local dual-bond factorization.

For 0 < r < 1, write a = artanh(r).  Up to the positive scale
r^(-1/2) / cosh(a), exp(a X) is the Ising bond matrix with diagonal
r^(-1/2) and off-diagonal r^(1/2).  Substituting r = exp(-2 beta) gives
exactly [[exp beta, exp(-beta)], [exp(-beta), exp beta]].

This gate licenses only the local 2x2 identity.  It does not license a
many-site factorization, a Jordan--Wigner transform, or a sector bound.
"""

from __future__ import annotations

import json
import sys

import sympy as sp


def fail(message: str, payload: object | None = None) -> "NoReturn":
    print(f"RESULT: FAIL: {message}", file=sys.stderr)
    if payload is not None:
        print(payload, file=sys.stderr)
    raise SystemExit(1)


def main() -> None:
    a = sp.symbols("a", real=True)
    r = sp.symbols("r", positive=True)
    X = sp.Matrix([[0, 1], [1, 0]])
    identity = sp.eye(2)

    exponential = (a * X).exp().applyfunc(sp.simplify)
    hyperbolic = sp.cosh(a) * identity + sp.sinh(a) * X
    exp_residual = (exponential - hyperbolic).applyfunc(sp.simplify)
    if exp_residual != sp.zeros(2):
        fail("exp(a X) did not reduce to cosh(a) I + sinh(a) X", exp_residual)

    # The Lean theorem assumes tanh(a) = r.  Since cosh(a) is positive,
    # this is exactly sinh(a) = r*cosh(a); substitute that relation before
    # applying the positive scalar.
    under_duality = hyperbolic.subs(sp.sinh(a), r * sp.cosh(a))
    scale = r ** sp.Rational(-1, 2) / sp.cosh(a)
    scaled = (scale * under_duality).applyfunc(sp.simplify)
    expected = sp.Matrix(
        [[r ** sp.Rational(-1, 2), r ** sp.Rational(1, 2)],
         [r ** sp.Rational(1, 2), r ** sp.Rational(-1, 2)]]
    )
    factor_residual = (scaled - expected).applyfunc(sp.simplify)
    if factor_residual != sp.zeros(2):
        fail("dual scaling did not produce the Ising bond matrix", factor_residual)

    certificate = {
        "status": "PASS",
        "classification": "symbolic gate for local 2x2 identity only",
        "exp_residual": [[str(x) for x in row] for row in exp_residual.tolist()],
        "factor_residual": [[str(x) for x in row] for row in factor_residual.tolist()],
        "assumptions": ["0 < r", "r < 1", "tanh(a) = r"],
    }
    print(json.dumps(certificate, sort_keys=True))


if __name__ == "__main__":
    main()
