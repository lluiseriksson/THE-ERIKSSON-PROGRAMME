#!/usr/bin/env python3
"""Finite model search for the F3 residual-only selector obstruction.

This is not a proof.  It is a bounded CSP search aligned with the Lean
`plaquetteGraph` adjacency: two concrete plaquettes are adjacent iff they are
distinct and their base sites have Euclidean lattice distance at most 1.
"""

from __future__ import annotations

from collections import defaultdict
from itertools import combinations, product
from math import dist

Vertex = tuple[tuple[int, ...], tuple[int, int]]
Bucket = frozenset[Vertex]


def vertices(d: int, L: int) -> list[Vertex]:
    dirs = list(combinations(range(d), 2))
    return [(site, direction) for site in product(range(L), repeat=d) for direction in dirs]


def adjacent(a: Vertex, b: Vertex) -> bool:
    return a != b and dist(a[0], b[0]) <= 1.0


def connected(bucket: Bucket) -> bool:
    if not bucket:
        return False
    seen = {next(iter(bucket))}
    stack = list(seen)
    while stack:
        x = stack.pop()
        for y in bucket:
            if y not in seen and adjacent(x, y):
                seen.add(y)
                stack.append(y)
    return len(seen) == len(bucket)


def anchored_buckets(vs: list[Vertex], root: Vertex, k: int) -> list[Bucket]:
    out: list[Bucket] = []
    rest = [v for v in vs if v != root]
    for combo in combinations(rest, k - 1):
        bucket = frozenset((root, *combo))
        if connected(bucket):
            out.append(bucket)
    return out


def safe_deletions(bucket: Bucket, root: Vertex) -> list[Vertex]:
    out = []
    for z in bucket:
        if z == root:
            continue
        residual = frozenset(v for v in bucket if v != z)
        if root in residual and connected(residual):
            out.append(z)
    return out


def residual_constraints(buckets: list[Bucket], root: Vertex) -> tuple[dict[Bucket, list[Vertex]], list[tuple[Bucket, list[Vertex]]]]:
    domains: dict[Bucket, set[Vertex]] = defaultdict(set)
    clauses: list[tuple[Bucket, list[Vertex]]] = []
    for bucket in buckets:
        clause: list[Vertex] = []
        for z in safe_deletions(bucket, root):
            residual = frozenset(v for v in bucket if v != z)
            domains[residual].update(residual)
            clause.append(z)
        clauses.append((bucket, clause))
    return {r: sorted(ps) for r, ps in domains.items()}, clauses


def csp_satisfiable(domains: dict[Bucket, list[Vertex]], clauses: list[tuple[Bucket, list[Vertex]]]) -> tuple[bool, dict[Bucket, Vertex]]:
    residuals = sorted(domains, key=lambda r: (len(domains[r]), len(r), sorted(r)))
    assignment: dict[Bucket, Vertex] = {}

    def clause_possible(bucket: Bucket, deleted: list[Vertex]) -> bool:
        for z in deleted:
            residual = frozenset(v for v in bucket if v != z)
            parent = assignment.get(residual)
            if parent is None:
                if any(adjacent(p, z) for p in domains.get(residual, ())):
                    return True
            elif adjacent(parent, z):
                return True
        return False

    def clause_satisfied(bucket: Bucket, deleted: list[Vertex]) -> bool:
        return any(
            (residual := frozenset(v for v in bucket if v != z)) in assignment
            and adjacent(assignment[residual], z)
            for z in deleted
        )

    def search(i: int) -> bool:
        if any(not clause_possible(bucket, deleted) for bucket, deleted in clauses):
            return False
        if i == len(residuals):
            return all(clause_satisfied(bucket, deleted) for bucket, deleted in clauses)
        residual = residuals[i]
        for parent in domains[residual]:
            assignment[residual] = parent
            if search(i + 1):
                return True
            del assignment[residual]
        return False

    return search(0), assignment.copy()


def run_case(d: int, L: int, k: int, root_index: int = 0) -> dict[str, object]:
    vs = vertices(d, L)
    root = vs[root_index]
    buckets = anchored_buckets(vs, root, k)
    domains, clauses = residual_constraints(buckets, root)
    sat, assignment = csp_satisfiable(domains, clauses)
    ambiguous = {
        residual: sorted(
            z for bucket, deleted in clauses for z in deleted
            if frozenset(v for v in bucket if v != z) == residual
        )
        for residual in domains
    }
    ambiguous_count = sum(1 for zs in ambiguous.values() if len(set(zs)) > 1)
    return {
        "d": d,
        "L": L,
        "k": k,
        "root": root,
        "vertices": len(vs),
        "anchored_connected_buckets": len(buckets),
        "residual_variables": len(domains),
        "clauses": len(clauses),
        "ambiguous_residuals": ambiguous_count,
        "satisfiable": sat,
        "sample_assignment_size": len(assignment),
    }


def main() -> int:
    cases = [
        (2, 2, 2),
        (2, 2, 3),
        (2, 3, 3),
        (3, 2, 3),
        (4, 1, 3),
        (4, 2, 3),
    ]
    for case in cases:
        print(run_case(*case), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
