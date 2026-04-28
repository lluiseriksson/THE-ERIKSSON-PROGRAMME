#!/usr/bin/env python3
"""Bounded search for residual parent-menu sizes in the F3 plaquette model.

This is empirical scaffolding, not a proof.  It uses the same finite plaquette
model as f3_residual_selector_counterexample_search.py and asks for the least
menu size M, in small cases, such that every anchored bucket has a safe deletion
whose residual has a selected adjacent parent in a residual-only menu of size M.

The second part computes a residual-local "forced menu" diagnostic: for each
residual R, enumerate all one-vertex extensions R ∪ {z} available in the finite
model and ask for the least number of parents in R covering those extension
vertices.  This is stronger/different than the global existential deletion
target, but it is useful for spotting growth patterns.
"""

from __future__ import annotations

from itertools import combinations

from f3_residual_selector_counterexample_search import (
    Bucket,
    Vertex,
    adjacent,
    anchored_buckets,
    csp_satisfiable,
    residual_constraints,
    safe_deletions,
    vertices,
)


def residual_parent_requirements(
    buckets: list[Bucket], root: Vertex
) -> tuple[dict[Bucket, set[Vertex]], list[tuple[Bucket, list[tuple[Bucket, Vertex]]]]]:
    domains: dict[Bucket, set[Vertex]] = {}
    clauses: list[tuple[Bucket, list[tuple[Bucket, Vertex]]]] = []
    for bucket in buckets:
        alternatives: list[tuple[Bucket, Vertex]] = []
        for z in safe_deletions(bucket, root):
            residual = frozenset(v for v in bucket if v != z)
            domains.setdefault(residual, set()).update(residual)
            alternatives.append((residual, z))
        clauses.append((bucket, alternatives))
    return domains, clauses


def subsets_of_size_at_most(items: list[Vertex], m: int) -> list[frozenset[Vertex]]:
    out: list[frozenset[Vertex]] = []
    start = 1 if m > 0 else 0
    for r in range(start, min(m, len(items)) + 1):
        out.extend(frozenset(c) for c in combinations(items, r))
    return out


def menu_csp_satisfiable(
    domains: dict[Bucket, set[Vertex]],
    clauses: list[tuple[Bucket, list[tuple[Bucket, Vertex]]]],
    m: int,
) -> tuple[bool, dict[Bucket, frozenset[Vertex]]]:
    residuals = sorted(domains, key=lambda r: (len(domains[r]), len(r), sorted(r)))
    choices = {
        residual: subsets_of_size_at_most(sorted(domains[residual]), m)
        for residual in residuals
    }
    assignment: dict[Bucket, frozenset[Vertex]] = {}

    def alternative_possible(residual: Bucket, z: Vertex) -> bool:
        menu = assignment.get(residual)
        if menu is None:
            return any(adjacent(p, z) for p in domains.get(residual, ()))
        return any(adjacent(p, z) for p in menu)

    def clause_possible(alternatives: list[tuple[Bucket, Vertex]]) -> bool:
        return any(alternative_possible(residual, z) for residual, z in alternatives)

    def search(i: int) -> bool:
        if any(not clause_possible(alternatives) for _, alternatives in clauses):
            return False
        if i == len(residuals):
            return True
        residual = residuals[i]
        # Try larger menus first; this finds witnesses quickly for small m.
        for menu in sorted(choices[residual], key=lambda s: (-len(s), sorted(s))):
            assignment[residual] = menu
            if search(i + 1):
                return True
            del assignment[residual]
        return False

    return search(0), assignment.copy()


def run_case(d: int, L: int, k: int, max_m: int | None = None) -> dict[str, object]:
    vs = vertices(d, L)
    root = vs[0]
    buckets = anchored_buckets(vs, root, k)
    domains, clauses = residual_parent_requirements(buckets, root)
    max_residual_card = max((len(r) for r in domains), default=0)
    limit = max_residual_card if max_m is None else min(max_m, max_residual_card)
    # M = 0 is impossible whenever there is a nonempty anchored bucket.
    min_menu = None
    witness_size = 0
    single_domains, single_clauses = residual_constraints(buckets, root)
    sat1, assignment1 = csp_satisfiable(single_domains, single_clauses)
    if sat1:
        min_menu = 1
        witness_size = len(assignment1)
    for m in range(2, limit + 1):
        if min_menu is not None:
            break
        if m >= max_residual_card:
            min_menu = m
            witness_size = len(domains)
            break
        sat, assignment = menu_csp_satisfiable(domains, clauses, m)
        if sat:
            min_menu = m
            witness_size = len(assignment)
            break
    return {
        "d": d,
        "L": L,
        "k": k,
        "vertices": len(vs),
        "anchored_connected_buckets": len(buckets),
        "residual_variables": len(domains),
        "max_residual_card": max_residual_card,
        "searched_menu_size_up_to": limit,
        "min_menu_size_found": min_menu,
        "witness_assignment_size": witness_size,
    }


def one_step_extension_vertices(residual: Bucket, vs: list[Vertex], root: Vertex) -> list[Vertex]:
    """Vertices z such that residual ∪ {z} is an anchored connected bucket.

    This ignores whether another deletion of the same bucket would satisfy the
    global target; it measures the residual frontier itself.
    """
    out: list[Vertex] = []
    for z in vs:
        if z in residual or z == root:
            continue
        bucket = frozenset((*residual, z))
        if root in residual and connected_cached(bucket):
            out.append(z)
    return out


_connected_cache: dict[Bucket, bool] = {}


def connected_cached(bucket: Bucket) -> bool:
    if bucket not in _connected_cache:
        from f3_residual_selector_counterexample_search import connected

        _connected_cache[bucket] = connected(bucket)
    return _connected_cache[bucket]


def min_parent_cover_size(residual: Bucket, extension_vertices: list[Vertex]) -> int | None:
    """Least number of parents in residual that cover all extension vertices."""
    if not extension_vertices:
        return 0
    parents = sorted(residual)
    for m in range(1, len(parents) + 1):
        for menu in combinations(parents, m):
            if all(any(adjacent(p, z) for p in menu) for z in extension_vertices):
                return m
    return None


def frontier_growth_case(d: int, L: int, residual_size: int, cap: int = 8) -> dict[str, object]:
    """Search residuals for large one-step frontier parent-cover numbers."""
    vs = vertices(d, L)
    root = vs[0]
    best: tuple[int, Bucket, list[Vertex]] = (0, frozenset(), [])
    checked = 0
    rest = [v for v in vs if v != root]
    for combo in combinations(rest, residual_size - 1):
        residual = frozenset((root, *combo))
        if not connected_cached(residual):
            continue
        checked += 1
        extensions = one_step_extension_vertices(residual, vs, root)
        if not extensions:
            continue
        cover = min_parent_cover_size(residual, extensions)
        if cover is not None and cover > best[0]:
            best = (cover, residual, extensions)
        if checked >= cap and d >= 3 and residual_size >= 4:
            # Keep the default run cheap; larger sweeps can be scripted later.
            break
    cover, residual, extensions = best
    return {
        "d": d,
        "L": L,
        "residual_size": residual_size,
        "connected_residuals_checked": checked,
        "max_one_step_frontier_parent_cover_found": cover,
        "best_residual": sorted(residual),
        "extension_vertices_for_best": sorted(extensions),
    }


def main() -> int:
    cases = [
        (2, 2, 2),
        (2, 2, 3),
        (2, 3, 3),
        (3, 2, 3),
        (4, 1, 3),
        (4, 2, 3),
        (2, 3, 4),
    ]
    for case in cases:
        print(run_case(*case), flush=True)
    print("--- residual-local frontier cover diagnostics ---", flush=True)
    frontier_cases = [
        (2, 3, 2),
        (2, 3, 3),
        (2, 4, 4),
        (3, 2, 3),
        (3, 2, 4),
        (4, 2, 3),
        (4, 2, 4),
    ]
    for case in frontier_cases:
        print(frontier_growth_case(*case), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
