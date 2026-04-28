# F3 low-cardinality bookkeeping totalization scope v2.118

**Task:** `CODEX-F3-LOWCARD-BOOKKEEPING-TOTALIZATION-SCOPE-001`  
**Date:** 2026-04-27  
**Status:** scope delivered; no Lean edit; no F3-COUNT status movement.

## Purpose

The v2.117 attempt showed that the high-cardinality branch of:

```lean
PhysicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296
```

is not the immediate blocker.  For `2 <= k`, existing safe-deletion APIs can
produce `deleted X`, the residual bucket, and a residual parent:

```lean
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_deletedVertex_has_residualNeighborParent
```

The remaining issue is the unguarded global image/subset payload in the v2.116
bookkeeping interface:

```lean
essential residual =
  ((plaquetteGraphPreconnectedSubsetsAnchoredCard
    physicalClayDimension L root k).filter
    (fun X => X.erase (deleted X) = residual)).image parentOf

essential residual ⊆ residual
```

Those clauses quantify over every `k`, including `k < 2`, while safe deletion
only starts at `2 <= k`.

## Existing low-cardinality Lean facts

The file already has base-cardinality structure:

```lean
plaquetteGraphPreconnectedSubsetsAnchoredCard_zero_eq_empty
plaquetteGraphPreconnectedSubsetsAnchoredCard_one_subset_singleton
plaquetteGraphPreconnectedSubsetsAnchoredCard_one_card_le_one
```

These facts separate the low-cardinality problem from safe deletion:

- for `k = 0`, the anchored family is empty;
- for `k = 1`, every current anchored bucket is `{root}`;
- no safe-deletion witness is needed or available in either branch.

## Recommended Lean target

Add a narrow interface:

```lean
def PhysicalPlaquetteGraphBaseAwareLowCardBookkeepingTotalization1296 : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L),
    ∃ fallbackDeleted : ConcretePlaquette physicalClayDimension L,
      fallbackDeleted ≠ root ∧
      ∀ k ≤ 1,
        ∃ deleted :
          Finset (ConcretePlaquette physicalClayDimension L) →
            ConcretePlaquette physicalClayDimension L,
        ∃ parentOf :
          Finset (ConcretePlaquette physicalClayDimension L) →
            ConcretePlaquette physicalClayDimension L,
        ∃ essential :
          Finset (ConcretePlaquette physicalClayDimension L) →
            Finset (ConcretePlaquette physicalClayDimension L),
          (∀ residual,
            essential residual =
              ((plaquetteGraphPreconnectedSubsetsAnchoredCard
                physicalClayDimension L root k).filter
                (fun X => X.erase (deleted X) = residual)).image parentOf) ∧
          (∀ residual, essential residual ⊆ residual)
```

The intended construction is:

```lean
deleted X := fallbackDeleted
parentOf X := root
essential residual :=
  ((plaquetteGraphPreconnectedSubsetsAnchoredCard
    physicalClayDimension L root k).filter
    (fun X => X.erase (deleted X) = residual)).image parentOf
```

For `k = 0`, the filter is empty by
`plaquetteGraphPreconnectedSubsetsAnchoredCard_zero_eq_empty`.

For `k = 1`, any current bucket `X` is `{root}` by
`plaquetteGraphPreconnectedSubsetsAnchoredCard_one_subset_singleton`; if
`fallbackDeleted ≠ root`, then `fallbackDeleted ∉ X` and:

```lean
parentOf X = root ∈ X.erase (deleted X)
```

This proves the required image/subset clause without pretending that safe
deletion applies.

## Missing local fact

The only new mathematical fact needed for the construction above is a uniform
non-root physical plaquette:

```lean
PhysicalPlaquetteGraphRootHasDistinctPlaquette
```

Suggested shape:

```lean
theorem physicalPlaquetteGraph_root_has_distinct_plaquette
    {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) :
    ∃ z : ConcretePlaquette physicalClayDimension L, z ≠ root
```

This should be proved from the concrete plaquette representation, not introduced
as an axiom.  A later proof can use it as the `fallbackDeleted`.

## Bridge back to bookkeeping

Once the low-card totalization and the already-existing high-card safe-deletion
branch are available, the bridge target should be:

```lean
physicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296_of_lowCardTotalization
```

or, if the proof is kept as one theorem:

```lean
physicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296
```

The bridge proof should split on `k ≤ 1`:

- low-card branch: use
  `PhysicalPlaquetteGraphBaseAwareLowCardBookkeepingTotalization1296`;
- high-card branch: use `2 <= k`, safe deletion, and
  `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_deletedVertex_has_residualNeighborParent`;
- define `essential` by the same residual-fiber image in both branches;
- prove `essential residual ⊆ residual` from the appropriate branch-specific
  parent-in-residual fact.

## Why this does not weaken v2.116

This scope does not change:

```lean
PhysicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296
physicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296_of_baseAwareBookkeeping_of_terminalPredecessorDomination1296
```

It only isolates the base cases needed to satisfy the existing unguarded v2.116
image/subset clauses.  The downstream bridge remains unchanged.

## Validation

No Lean file was edited in this scope task, so no `lake build` was required.

## Non-claims

This task does not prove:

- `PhysicalPlaquetteGraphBaseAwareLowCardBookkeepingTotalization1296`;
- `physicalPlaquetteGraph_root_has_distinct_plaquette`;
- `PhysicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296`;
- `PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296`;
- any decoder compression to an older constant.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No ledger status, project percentage,
README metric, planner metric, or Clay-level claim moved.
