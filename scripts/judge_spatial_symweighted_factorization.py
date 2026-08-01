"""Exact gate for one theorem: the ring-weighted dual factorisation.

The proposed Lean theorem may combine the already certified finite-product
dual-bond identity with the exact square root of the periodic ring weight.
This gate checks that composition exhaustively for every pair of two-state
ring configurations at 1,...,6 sites, using exact SymPy expressions.

The gate rejects three known mutations: an extra local scale, omission of the
closing bond on the source ring, and omission of the closing bond on the target
ring.  It licenses only one entrywise factorisation of ``symWeighted``.  It
does not license a Clifford/Jordan--Wigner representation, a norm estimate, or
either sector/spectral bound.
"""

from __future__ import annotations

import itertools
import json
import sys
from typing import NoReturn

import sympy as sp


def fail(message: str, payload: object | None = None) -> NoReturn:
    print(f"RESULT: FAIL: {message}", file=sys.stderr)
    if payload is not None:
        print(payload, file=sys.stderr)
    raise SystemExit(1)


def bond_sign(left: int, right: int) -> int:
    return 1 if left == right else -1


def ring_energy(configuration: tuple[int, ...]) -> int:
    size = len(configuration)
    return sum(
        bond_sign(configuration[j], configuration[(j + 1) % size])
        for j in range(size)
    )


def open_energy(configuration: tuple[int, ...]) -> int:
    return sum(
        bond_sign(configuration[j], configuration[j + 1])
        for j in range(len(configuration) - 1)
    )


def main() -> None:
    x = sp.symbols("x", positive=True)
    scale, diagonal, off_diagonal = sp.symbols(
        "scale diagonal off_diagonal", nonzero=True
    )
    checked = 0
    scale_mutations_rejected = 0
    source_closure_mutations_rejected = 0
    target_closure_mutations_rejected = 0

    for size in range(1, 7):
        configurations = list(itertools.product((0, 1), repeat=size))
        for sigma in configurations:
            source_half = sp.sqrt(x ** ring_energy(sigma))
            source_exponential = x ** sp.Rational(ring_energy(sigma), 2)
            if sp.simplify(source_half - source_exponential) != 0:
                fail("source square-root rewrite failed", {"size": size, "sigma": sigma})

            for tau in configurations:
                target_half = sp.sqrt(x ** ring_energy(tau))
                target_exponential = x ** sp.Rational(ring_energy(tau), 2)
                if sp.simplify(target_half - target_exponential) != 0:
                    fail("target square-root rewrite failed", {"size": size, "tau": tau})

                dual_entries = [
                    diagonal if left == right else off_diagonal
                    for left, right in zip(sigma, tau, strict=True)
                ]
                local_product = sp.prod(scale * entry for entry in dual_entries)
                weighted_kernel = source_half * local_product * target_half
                factorised = (
                    source_exponential
                    * scale**size
                    * sp.prod(dual_entries)
                    * target_exponential
                )
                if sp.simplify(weighted_kernel - factorised) != 0:
                    fail(
                        "ring-weighted dual factorisation failed",
                        {"size": size, "sigma": sigma, "tau": tau},
                    )

                scale_mutation = (
                    source_exponential
                    * scale ** (size + 1)
                    * sp.prod(dual_entries)
                    * target_exponential
                )
                if sp.simplify(weighted_kernel - scale_mutation) == 0:
                    fail("gate accepted the size -> size+1 scale mutation")
                scale_mutations_rejected += 1

                source_open_mutation = (
                    x ** sp.Rational(open_energy(sigma), 2)
                    * scale**size
                    * sp.prod(dual_entries)
                    * target_exponential
                )
                if sp.simplify(weighted_kernel - source_open_mutation) == 0:
                    fail("gate accepted omission of the source closing bond")
                source_closure_mutations_rejected += 1

                target_open_mutation = (
                    source_exponential
                    * scale**size
                    * sp.prod(dual_entries)
                    * x ** sp.Rational(open_energy(tau), 2)
                )
                if sp.simplify(weighted_kernel - target_open_mutation) == 0:
                    fail("gate accepted omission of the target closing bond")
                target_closure_mutations_rejected += 1
                checked += 1

    expected = sum(4**size for size in range(1, 7))
    counters = {
        "configuration_pairs_checked": checked,
        "scale_mutations_rejected": scale_mutations_rejected,
        "source_closing_bond_mutations_rejected": source_closure_mutations_rejected,
        "target_closing_bond_mutations_rejected": target_closure_mutations_rejected,
    }
    for name, actual in counters.items():
        if actual != expected:
            fail("wrong exhaustive counter", {"counter": name, "actual": actual, "expected": expected})

    print(json.dumps({
        "status": "PASS",
        "classification": "exact symWeighted ring/dual factorisation gate only",
        "ring_sizes": list(range(1, 7)),
        **counters,
    }, sort_keys=True))


if __name__ == "__main__":
    main()
