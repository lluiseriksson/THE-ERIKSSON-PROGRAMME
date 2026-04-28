# F3 Residual Parent-Menu Cover Attempt v2.76

Timestamp: 2026-04-27T05:45:00Z

Task: `CODEX-F3-PROVE-RESIDUAL-PARENT-MENU-COVER-001`

## Target

Attempted target:

```lean
PhysicalPlaquetteGraphResidualParentMenuCovers1296
```

This target would feed the v2.75 bridge:

```lean
physicalPlaquetteGraphSymbolicResidualParentSelector1296_of_residualParentMenuCovers1296
```

and then the v2.73 strengthened product-symbol decoder:

```lean
physicalPlaquetteGraphDeletedVertexDecoderStep1296x1296_of_symbolicResidualParentSelector1296
```

## No-Closure Result

No proof was added.  The target is stronger than the currently available local
branching facts.

The project has a physical local degree bound:

```lean
plaquetteGraph_neighborFinset_card_le_physical_ternary
```

and a local witness theorem:

```lean
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_deletedVertex_has_residualNeighborParent
```

Together they say: once a deleted vertex `z` and current bucket `X` are known,
there exists some residual parent `p ∈ X.erase z` adjacent to `z`, and the
neighbors of a fixed `p` can be locally coded by `Fin 1296`.

The menu-cover target needs a different uniform bound:

```text
for each residual R, at most 1296 parent candidates cover all safe extensions
X = R ∪ {z}
```

That is a bound on the residual frontier-parent menu, not on the local degree of
one chosen parent.  No existing theorem in `LatticeAnimalCount.lean` bounds this
frontier-parent menu by `1296`.

## Why Enumeration of the Residual Is Not Enough

A tempting construction is:

```text
parent R : Fin 1296 -> Option plaquette
```

by enumerating `R`.  This would require `R.card ≤ 1296`.  But in the target,
`k` is arbitrary and `R` has cardinality `k - 1`; no such bound is available or
expected.

The available local degree bound instead controls:

```text
{z | z adjacent to a fixed parent p}
```

not:

```text
{p ∈ R | p can serve as a parent for some safe extension of R}
```

## Exact Remaining Blocker

The missing theorem is a residual-frontier menu bound:

```lean
PhysicalPlaquetteGraphResidualParentMenuBound1296
```

Suggested informal statement:

For each physical residual bucket `R` arising from an anchored safe deletion,
there is a residual-only finset `S(R) ⊆ R` with `S(R).card ≤ 1296` such that
every relevant current anchored bucket producing `R` has a safe deleted
plaquette adjacent to some `p ∈ S(R)`.

If this theorem is false, the next honest route is to strengthen the first
symbol component beyond `Fin 1296`, for example to encode a bounded residual
parent menu whose size depends on a proved frontier bound.

## Validation

Build:

```powershell
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result:

```text
Build completed successfully (8184 jobs).
```

No new theorem was added, so there is no new axiom trace.  The existing v2.75
bridge remains pinned to:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`.  No new project axiom.

## Project Status

`F3-COUNT` remains `CONDITIONAL_BRIDGE`.  The old `Fin 1296` decoder contract is
not claimed, and the strengthened product-symbol route remains open at the
parent-menu-cover theorem.  No Clay, lattice, honest-discount, named-frontier,
README, or planner percentage moved.

Recommended next task:

```text
CODEX-F3-RESIDUAL-PARENT-MENU-BOUND-SCOPE-001
```
