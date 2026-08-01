"""Exact gate for one theorem: exponential form of the periodic ring weight.

For every two-state ring configuration, the product of bond weights
``exp(gamma * sign_j)`` must equal ``exp(gamma * sum_j sign_j)``.  The gate
checks the periodic indexing exhaustively for ring sizes 1,...,8 and rejects a
known mutation that omits the closing bond.

This licenses only the exact exponential rewrite of ``spatialWeightRing``.
It does not license a square-root rewrite, a weighted-kernel factorisation,
Jordan--Wigner, or a sector/spectral estimate.
"""

from __future__ import annotations

import itertools
import json
import sys

import sympy as sp


def fail(message: str, payload: object | None = None) -> "NoReturn":
    print(f"RESULT: FAIL: {message}", file=sys.stderr)
    if payload is not None:
        print(payload, file=sys.stderr)
    raise SystemExit(1)


def bond_sign(left: int, right: int) -> int:
    return 1 if left == right else -1


def main() -> None:
    x = sp.symbols("x", positive=True)
    checked = 0
    closure_mutations_rejected = 0

    for size in range(1, 9):
        for sigma in itertools.product((0, 1), repeat=size):
            signs = [
                bond_sign(sigma[j], sigma[(j + 1) % size])
                for j in range(size)
            ]
            product_weight = sp.prod(x**sign for sign in signs)
            exponential_weight = x ** sum(signs)
            residual = sp.cancel(product_weight - exponential_weight)
            if residual != 0:
                fail(
                    "periodic product did not equal the exponential of the bond sum",
                    {"size": size, "sigma": sigma, "residual": str(residual)},
                )

            open_chain_mutation = sp.prod(x**sign for sign in signs[:-1])
            mutated_residual = sp.cancel(open_chain_mutation - exponential_weight)
            if mutated_residual == 0:
                fail(
                    "gate accepted omission of the closing bond",
                    {"size": size, "sigma": sigma},
                )
            closure_mutations_rejected += 1
            checked += 1

    expected = sum(2**size for size in range(1, 9))
    if checked != expected:
        fail("wrong configuration count", {"actual": checked, "expected": expected})
    if closure_mutations_rejected != expected:
        fail(
            "wrong closure-mutation count",
            {"actual": closure_mutations_rejected, "expected": expected},
        )

    print(json.dumps({
        "status": "PASS",
        "classification": "exact periodic ring-weight gate only",
        "ring_sizes": list(range(1, 9)),
        "configurations_checked": checked,
        "closing_bond_mutations_rejected": closure_mutations_rejected,
    }, sort_keys=True))


if __name__ == "__main__":
    main()
