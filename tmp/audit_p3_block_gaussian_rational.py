#!/usr/bin/env python3
"""Exact rational counter-check of the scratch P3 block-Gaussian contract.

This is a lightweight semantic test, not compiler evidence.  It chooses a
non-diagonal fine precision and a nontrivial proper projector, constructs all
three inverses internally, and checks the two printed recurrences exactly.
"""

from fractions import Fraction as F
import hashlib
import json


def eye(n):
    return [[F(i == j) for j in range(n)] for i in range(n)]


def zero(rows, cols):
    return [[F(0) for _ in range(cols)] for _ in range(rows)]


def shape(a):
    return len(a), len(a[0])


def add(a, b):
    return [[x + y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def sub(a, b):
    return [[x - y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def smul(c, a):
    return [[c * x for x in row] for row in a]


def mul(a, b):
    ar, ac = shape(a)
    br, bc = shape(b)
    assert ac == br
    return [[sum((a[i][k] * b[k][j] for k in range(ac)), F(0))
             for j in range(bc)] for i in range(ar)]


def transpose(a):
    return [list(row) for row in zip(*a)]


def inverse(a):
    n, m = shape(a)
    assert n == m
    aug = [row[:] + ident[:] for row, ident in zip(a, eye(n))]
    for col in range(n):
        pivot = next((r for r in range(col, n) if aug[r][col] != 0), None)
        if pivot is None:
            raise ValueError("singular matrix")
        aug[col], aug[pivot] = aug[pivot], aug[col]
        p = aug[col][col]
        aug[col] = [x / p for x in aug[col]]
        for r in range(n):
            if r == col:
                continue
            q = aug[r][col]
            if q:
                aug[r] = [x - q * y for x, y in zip(aug[r], aug[col])]
    return [row[n:] for row in aug]


def is_zero(a):
    return all(x == 0 for row in a for x in row)


def assert_eq(label, a, b):
    residual = sub(a, b)
    if not is_zero(residual):
        raise AssertionError(f"{label}: residual={residual}")


def encoded(a):
    return [[f"{x.numerator}/{x.denominator}" for x in row] for row in a]


def main():
    # H = K = Q^3, L = Q^2.  R selects two coordinates, so R Rdag = I
    # while P = Rdag R is a proper, nontrivial projector.
    A = [[F(5), F(1), F(1)],
         [F(1), F(6), F(2)],
         [F(1), F(2), F(8)]]
    Q = [[F(1), F(1), F(0)],
         [F(0), F(1), F(1)],
         [F(1), F(0), F(1)]]
    Qdag = transpose(Q)
    R = [[F(1), F(0), F(0)],
         [F(0), F(1), F(0)]]
    Rdag = transpose(R)
    P = mul(Rdag, R)
    b, c = F(2), F(3)
    beta = b * c / (b + c)

    assert_eq("coisometry", mul(R, Rdag), eye(2))
    assert_eq("projector", mul(P, P), P)

    Kb = add(A, smul(b, mul(Qdag, Q)))
    G = inverse(Kb)
    S = mul(Q, mul(G, Qdag))
    D = sub(smul(b, eye(3)), smul(b * b, S))
    Cprec = add(D, smul(c, P))
    C = inverse(Cprec)
    Knext = add(A, smul(beta, mul(Qdag, mul(P, Q))))
    Gnext = inverse(Knext)

    candidate = add(G, smul(b * b, mul(G, mul(Qdag, mul(C, mul(Q, G))))))

    assert_eq("fine right inverse", mul(Kb, G), eye(3))
    assert_eq("fine left inverse", mul(G, Kb), eye(3))
    assert_eq("coarse right inverse", mul(Cprec, C), eye(3))
    assert_eq("coarse left inverse", mul(C, Cprec), eye(3))
    assert_eq("next right inverse", mul(Knext, candidate), eye(3))
    assert_eq("next left inverse", mul(candidate, Knext), eye(3))
    assert_eq("Eq. (2.42)", Gnext, candidate)

    lhs241 = mul(R, mul(Q, Gnext))
    rhs241 = smul(b + c, mul(R, mul(C, mul(Q, G))))
    assert_eq("Eq. (2.41) orientation", lhs241, rhs241)

    # Ensure the fixture detects an order error: C and S do not commute.
    if is_zero(sub(mul(S, C), mul(C, S))):
        raise AssertionError("degenerate fixture: S and C commute")
    wrong_beta = beta + 1
    wrong_next = add(A, smul(wrong_beta, mul(Qdag, mul(P, Q))))
    if is_zero(sub(mul(wrong_next, candidate), eye(3))):
        raise AssertionError("degenerate fixture: scalar recurrence is not live")
    wrong_candidate = add(G, smul(b * b, mul(G, mul(Qdag, mul(C, Q)))))
    if is_zero(sub(mul(Knext, wrong_candidate), eye(3))):
        raise AssertionError("degenerate fixture: terminal Green factor is not live")

    payload = {
        "beta": f"{beta.numerator}/{beta.denominator}",
        "Gnext": encoded(Gnext),
        "candidate": encoded(candidate),
        "lhs241": encoded(lhs241),
        "rhs241": encoded(rhs241),
    }
    digest = hashlib.sha256(
        json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest().upper()
    print("P3_BLOCK_GAUSSIAN_RATIONAL_OK", f"sha256={digest}")


if __name__ == "__main__":
    main()
