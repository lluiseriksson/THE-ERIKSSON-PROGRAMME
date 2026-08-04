"""Symbolic audit of the scaled right-edge target identity."""

import sympy as sp


def verify():
    A, B, Ad, Bd, delta, lam = sp.symbols(
        "A B Ad Bd delta lambda", nonzero=True)
    # Q=A/(2 delta B), d=lambda*delta, hence d/dlambda=delta*d/dd.
    q_lambda = sp.cancel(
        delta * (Ad*(2*delta*B)-A*(2*delta*Bd))
        / (2*delta*B)**2)
    assert sp.cancel(q_lambda-(Ad*B-A*Bd)/(2*B**2)) == 0
    W = 2*(A*Bd-Ad*B)
    assert sp.cancel(q_lambda+W/(4*B**2)) == 0
    print(
        "SCALED RIGHT-EDGE TARGET PASS: Q_lambda=-W/(4 B^2); "
        "zero-face interval certificate remains required"
    )


if __name__ == "__main__":
    verify()
