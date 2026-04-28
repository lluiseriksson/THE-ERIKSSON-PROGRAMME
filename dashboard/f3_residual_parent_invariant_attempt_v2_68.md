# F3 B.2 v2.68 Residual Parent Invariant Attempt

**Task**: `CODEX-F3-PROVE-RESIDUAL-PARENT-INVARIANT-001`
**Date**: 2026-04-26T17:10:00Z
**Status**: `NO_CLOSURE` for the full invariant; local residual-parent lemma landed.
**Ledger status**: `F3-COUNT` remains `CONDITIONAL_BRIDGE`.

## Target

The attempted target was:

```lean
PhysicalPlaquetteGraphResidualParentInvariant1296
```

This asks for a single residual-only parent selector:

```lean
Finset (ConcretePlaquette physicalClayDimension L) ->
  Option (ConcretePlaquette physicalClayDimension L)
```

such that every nontrivial anchored bucket admits a safe deleted plaquette
whose residual parent is the selected one.

## New Lean Helper Landed

Codex proved the local frontier fact:

```lean
plaquetteGraphPreconnectedSubsetsAnchoredCard_deletedVertex_has_residualNeighborParent
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_deletedVertex_has_residualNeighborParent
```

Meaning: if `z` is a non-root member of an anchored preconnected bucket `X`,
then some parent `p ∈ X.erase z` is adjacent to `z`.

This closes the local adjacency part of the residual-parent story.  It does
not choose a canonical parent depending only on the residual bucket.

## Validation

Build:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result: 8184/8184 jobs green.

Pinned traces:

```text
YangMills.plaquetteGraphPreconnectedSubsetsAnchoredCard_deletedVertex_has_residualNeighborParent
depends on axioms: [propext, Classical.choice, Quot.sound]

YangMills.physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_deletedVertex_has_residualNeighborParent
depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry`. No project axiom.

## Why The Full Invariant Did Not Close

The local lemma proves:

```lean
∀ X z, z ∈ X -> z ≠ root ->
  ∃ p, p ∈ X.erase z ∧ z ∈ neighborFinset p
```

The v2.67 invariant needs more:

```lean
∃ parent : residual -> Option p, ...
```

where the selected parent must depend only on the residual bucket, not on the
particular original bucket/deleted vertex witness chosen after the fact.

Choosing a parent by `Classical.choose` from the current `(X,z)` would be a
post-hoc existential shortcut.  Choosing a parent from the residual by searching
over possible extensions is also insufficient without proving that this selected
parent works for the current bucket's admissible deletion.  Multiple valid
extensions can share the same residual, so residual-only canonicity is a real
extra theorem.

## Exact Remaining Theorem

The remaining theorem is still:

```lean
PhysicalPlaquetteGraphResidualParentInvariant1296
```

but the next narrowed form should prove a canonical selector, for example:

```lean
-- Candidate shape:
-- define a residual frontier order/minimum parent p(R), then prove that for
-- every anchored bucket X there is a safe deletion z such that
-- z ∈ neighborFinset (p (X.erase z)).
```

Any proof must avoid selecting `z` or `p` from the current bucket after the
residual symbol is supposedly fixed.

## Project Impact

This is a local mathematical narrowing, not a decoder closure.
`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No Clay-level, lattice-level,
honest-discount, or named-frontier percentage moves from this entry.
