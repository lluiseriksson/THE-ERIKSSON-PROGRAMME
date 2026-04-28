# F3 low-cardinality bookkeeping totalization proof v2.120

**Task:** `CODEX-F3-PROVE-LOWCARD-BOOKKEEPING-TOTALIZATION-001`  
**Date:** 2026-04-27  
**Status:** Lean proof closed; no F3-COUNT status movement.

## Lean identifiers proved

```lean
physicalPlaquetteGraph_root_has_distinct_plaquette
physicalPlaquetteGraph_baseAwareLowCardBookkeepingTotalization1296
```

Locations:

```text
YangMills/ClayCore/LatticeAnimalCount.lean:4716
YangMills/ClayCore/LatticeAnimalCount.lean:4751
YangMills/ClayCore/LatticeAnimalCount.lean:5710
YangMills/ClayCore/LatticeAnimalCount.lean:5711
```

## Proof summary

`physicalPlaquetteGraph_root_has_distinct_plaquette` proves
`PhysicalPlaquetteGraphRootHasDistinctPlaquette` from the concrete physical
plaquette representation.  In physical dimension `4`, it constructs two
same-site orientation candidates `(0,1)` and `(0,2)`; at least one is distinct
from the root.

`physicalPlaquetteGraph_baseAwareLowCardBookkeepingTotalization1296` proves
`PhysicalPlaquetteGraphBaseAwareLowCardBookkeepingTotalization1296` by:

- choosing the non-root fallback plaquette from
  `physicalPlaquetteGraph_root_has_distinct_plaquette`;
- setting `deleted X := fallbackDeleted`;
- setting `parentOf X := root`;
- defining `essential residual` as the required residual-fiber image;
- using `plaquetteGraphPreconnectedSubsetsAnchoredCard_zero_eq_empty` for
  `k = 0`;
- using `plaquetteGraphPreconnectedSubsetsAnchoredCard_one_subset_singleton`
  for `k = 1`, so every current bucket is `{root}` and
  `root ∈ X.erase fallbackDeleted`.

The proof does not invoke safe deletion in the `k < 2` branch and does not use
an arbitrary default that bypasses `parentOf X ∈ X.erase (deleted X)`.

## Validation

Command run:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result: passed.

The new theorem-specific axiom traces are:

```text
YangMills.physicalPlaquetteGraph_root_has_distinct_plaquette:
  [propext, Classical.choice, Quot.sound]

YangMills.physicalPlaquetteGraph_baseAwareLowCardBookkeepingTotalization1296:
  [propext, Classical.choice, Quot.sound]
```

## Next bridge target

The next natural Lean target is to combine this low-cardinality branch with the
existing `2 <= k` safe-deletion branch:

```lean
PhysicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296
```

This should not move `F3-COUNT` by itself.  The downstream chain still also
requires the residual terminal-predecessor domination theorem and a Cowork audit
of the strengthened decoder route/constants.

## Non-claims

This task does not prove:

- `PhysicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296`;
- `PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296`;
- `PhysicalPlaquetteGraphDeletedVertexDecoderStep1296x1296x1296`;
- any compression to the older `1296` or `1296 x 1296` constants.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No ledger status, project percentage,
README metric, planner metric, or Clay-level claim moved.
