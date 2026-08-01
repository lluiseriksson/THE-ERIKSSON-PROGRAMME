"""Exact gate for one theorem: lift the dual-bond identity to a finite product.

The proposed Lean theorem may rewrite the product defining ``spatialKernel``
as ``scale ** L`` times the product of the dual-field entries.  This gate
checks that algebra exhaustively for every pair of two-state configurations at
L = 0,...,6, using exact SymPy expressions.

This licenses only the finite-product identity.  It does not license the
weighted ring operator, a tensor-product exponential, Jordan--Wigner, or a
sector/spectral estimate.
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


def main() -> None:
    scale, diagonal, off_diagonal = sp.symbols(
        "scale diagonal off_diagonal", nonzero=True
    )
    checked = 0
    mutation_rejections = 0

    for length in range(7):
        configurations = list(itertools.product((0, 1), repeat=length))
        for sigma in configurations:
            for tau in configurations:
                dual_entries = [
                    diagonal if left == right else off_diagonal
                    for left, right in zip(sigma, tau, strict=True)
                ]
                local_entries = [scale * entry for entry in dual_entries]
                local_product = sp.prod(local_entries)
                lifted_product = scale**length * sp.prod(dual_entries)
                residual = sp.expand(local_product - lifted_product)
                if residual != 0:
                    fail(
                        "finite-product factorisation failed",
                        {"length": length, "sigma": sigma, "tau": tau,
                         "residual": str(residual)},
                    )

                # A known exponent mutation must be detected away from L = 0.
                if length > 0:
                    mutated = sp.expand(
                        local_product - scale ** (length + 1) * sp.prod(dual_entries)
                    )
                    if mutated == 0:
                        fail(
                            "gate accepted the L -> L+1 exponent mutation",
                            {"length": length, "sigma": sigma, "tau": tau},
                        )
                    mutation_rejections += 1
                checked += 1

    expected_checks = sum(4**length for length in range(7))
    expected_mutations = expected_checks - 1
    if checked != expected_checks:
        fail("wrong exhaustive-check count", {"actual": checked, "expected": expected_checks})
    if mutation_rejections != expected_mutations:
        fail(
            "wrong mutation-rejection count",
            {"actual": mutation_rejections, "expected": expected_mutations},
        )

    print(json.dumps({
        "status": "PASS",
        "classification": "exact finite-product gate only",
        "lengths": [0, 1, 2, 3, 4, 5, 6],
        "configuration_pairs_checked": checked,
        "known_exponent_mutations_rejected": mutation_rejections,
    }, sort_keys=True))


if __name__ == "__main__":
    main()
