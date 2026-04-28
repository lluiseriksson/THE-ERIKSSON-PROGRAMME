# F3 Symbolic Parent Selector Attempt v2.74

Timestamp: 2026-04-27T05:05:00Z

Task: `CODEX-F3-PROVE-SYMBOLIC-PARENT-SELECTOR-001`

## Target

Attempted target:

```lean
PhysicalPlaquetteGraphSymbolicResidualParentSelector1296
```

This target would close the v2.73 product-symbol bridge:

```lean
physicalPlaquetteGraphDeletedVertexDecoderStep1296x1296_of_symbolicResidualParentSelector1296
```

but only for the strengthened alphabet `Fin 1296 × Fin 1296`.  It would not
prove the original `PhysicalPlaquetteGraphDeletedVertexDecoderStep1296`.

## No-Closure Result

No proof was added.  The available lemmas give the wrong dependency direction.

The existing local frontier lemma:

```lean
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_deletedVertex_has_residualNeighborParent
```

says that after a current bucket `X` and deleted vertex `z` are chosen, there is
some parent `p ∈ X.erase z` adjacent to `z`.

The symbolic selector needs more:

```lean
parent :
  Finset (ConcretePlaquette physicalClayDimension L) ->
  Fin 1296 -> Option (ConcretePlaquette physicalClayDimension L)
```

fixed before the current extension is inspected, such that every current bucket
has at least one safe deleted vertex whose residual-neighbor parent lies in the
1296-element menu selected for that residual.

Equivalently, for every residual bucket `R`, one needs a residual-only finite
parent menu:

```text
S(R) = {p | ∃ symbol : Fin 1296, parent R symbol = some p}
```

with `|S(R)| <= 1296`, and every relevant current extension must admit a safe
deleted vertex adjacent to some parent in `S(R)`.

This is not supplied by v2.68's local neighbor-parent lemma.  That lemma picks
`p` after `z`; it does not produce a 1296-bounded menu of parents depending only
on the residual.

## Exact Remaining Blocker

Name for the missing combinatorial content:

```lean
PhysicalPlaquetteGraphResidualParentMenuCovers1296
```

Informal statement:

For every physical root/cardinality and every residual bucket that can occur
after safe deletion, there is a residual-only set/function of at most 1296 parent
candidates such that every compatible current anchored bucket has a safe deleted
plaquette adjacent to one of those parent candidates.

This is strictly stronger than the local post-hoc parent existence theorem and
is the true remaining content behind the v2.73 symbolic selector.

## Why Not Use `Classical.choose`

Choosing a parent from the current witness `(X,z)` would be an existential-only
decoder and would violate the task stop condition.  It would also fail to define
the required fixed function:

```lean
residual -> Fin 1296 -> Option parent
```

before the current extension is known.

## Project Status

No Lean theorem was added in this attempt.  No `sorry` or project axiom was
introduced.  `F3-COUNT` remains `CONDITIONAL_BRIDGE`.

Build:

```powershell
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result:

```text
Build completed successfully (8184 jobs).
```

No Clay, lattice, honest-discount, named-frontier, README, or planner
percentage moved.

Recommended next task:

```text
CODEX-F3-RESIDUAL-PARENT-MENU-COVER-SCOPE-001
```

Its goal should be to define the missing menu-cover proposition precisely and
search for either a proof route or a finite counterexample pattern.
