#!/usr/bin/env python3
"""Bounded search for selected last-edge predecessor image growth.

This is empirical scaffolding for the F3 base-aware decoder route, not a proof.
It reuses the finite plaquette model from
`f3_residual_selector_counterexample_search.py`, whose adjacency matches the
Lean `plaquetteGraph`: distinct concrete plaquettes are adjacent when their
base-site lattice distance is at most one.

For a connected anchored residual R, this script computes a residual-only
diagnostic:

* all one-step extension vertices z such that R union {z} remains connected;
* the essential parent set E(R), consisting of residual vertices adjacent to at
  least one such z;
* the least size of a terminal-predecessor image P subset R such that every
  parent p in E(R) is adjacent to some q in P.

This deliberately differs from the raw residual frontier, residual size, local
degree of one fixed portal, and first-shell reachability.  A bounded no-growth
result from this script must not be treated as a Lean proof.
"""

from __future__ import annotations

from itertools import combinations
from typing import Iterable

from f3_residual_selector_counterexample_search import (
    Bucket,
    Vertex,
    adjacent,
    connected,
    vertices,
)


def anchored_connected_residuals(
    vs: list[Vertex], root: Vertex, residual_size: int, cap: int | None = None
) -> Iterable[Bucket]:
    """Yield anchored connected residuals of fixed cardinality."""
    if residual_size < 1:
        return
    checked = 0
    rest = [v for v in vs if v != root]
    for combo in combinations(rest, residual_size - 1):
        residual = frozenset((root, *combo))
        if connected(residual):
            yield residual
            checked += 1
            if cap is not None and checked >= cap:
                return


def one_step_extensions(residual: Bucket, vs: list[Vertex], root: Vertex) -> list[Vertex]:
    """Residual-only one-step extensions preserving anchored connectedness."""
    if root not in residual or not connected(residual):
        return []
    out: list[Vertex] = []
    for z in vs:
        if z in residual or z == root:
            continue
        bucket = frozenset((*residual, z))
        if connected(bucket):
            out.append(z)
    return out


def essential_parents(residual: Bucket, extensions: list[Vertex]) -> list[Vertex]:
    """Residual parents supporting at least one one-step extension."""
    return sorted(p for p in residual if any(adjacent(p, z) for z in extensions))


def min_terminal_predecessor_image(
    residual: Bucket, parents: list[Vertex]
) -> tuple[int | None, frozenset[Vertex]]:
    """Least predecessor image covering parents by residual-local last edges."""
    if not parents:
        return 0, frozenset()
    candidates = sorted(residual)
    parent_bits: dict[Vertex, int] = {p: 1 << i for i, p in enumerate(parents)}
    covers: list[tuple[Vertex, int]] = []
    full = (1 << len(parents)) - 1
    for q in candidates:
        mask = 0
        for p in parents:
            if adjacent(q, p):
                mask |= parent_bits[p]
        if mask:
            covers.append((q, mask))
    for m in range(1, len(covers) + 1):
        for combo in combinations(covers, m):
            mask = 0
            chosen = []
            for q, qmask in combo:
                mask |= qmask
                chosen.append(q)
            if mask == full:
                return m, frozenset(chosen)
    return None, frozenset()


def run_case(
    d: int,
    L: int,
    residual_size: int,
    cap: int | None = None,
    root_index: int = 0,
) -> dict[str, object]:
    vs = vertices(d, L)
    root = vs[root_index]
    best: dict[str, object] = {
        "d": d,
        "L": L,
        "residual_size": residual_size,
        "vertices": len(vs),
        "root": root,
        "connected_residuals_checked": 0,
        "max_min_terminal_predecessor_image": 0,
        "best_residual": [],
        "best_essential_parent_count": 0,
        "best_extension_count": 0,
        "best_selected_predecessors": [],
        "unchecked_reason": None,
    }
    for residual in anchored_connected_residuals(vs, root, residual_size, cap):
        best["connected_residuals_checked"] = int(best["connected_residuals_checked"]) + 1
        extensions = one_step_extensions(residual, vs, root)
        parents = essential_parents(residual, extensions)
        cover_size, chosen = min_terminal_predecessor_image(residual, parents)
        if cover_size is None:
            best["unchecked_reason"] = "some essential parent has no residual-local terminal predecessor"
            continue
        if cover_size > int(best["max_min_terminal_predecessor_image"]):
            best.update(
                {
                    "max_min_terminal_predecessor_image": cover_size,
                    "best_residual": sorted(residual),
                    "best_essential_parent_count": len(parents),
                    "best_extension_count": len(extensions),
                    "best_selected_predecessors": sorted(chosen),
                }
            )
    return best


def main() -> int:
    cases = [
        # Exhaustive tiny cases.
        (2, 3, 2, None),
        (2, 3, 3, None),
        (2, 4, 4, None),
        (3, 2, 3, None),
        (3, 2, 4, None),
        # Physical dimension cases.  The size-4/5 searches are capped to keep
        # the default diagnostic cheap and reproducible.
        (4, 1, 3, None),
        (4, 2, 3, None),
        (4, 2, 4, 2500),
        (4, 2, 5, 2500),
    ]
    for case in cases:
        print(run_case(*case), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
