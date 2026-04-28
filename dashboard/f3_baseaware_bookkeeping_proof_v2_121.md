# F3 base-aware bookkeeping proof v2.121

**Task:** `CODEX-F3-PROVE-BASEAWARE-BOOKKEEPING-WITH-LOWCARD-001`  
**Date:** 2026-04-27  
**Status:** Lean proof closed; no F3-COUNT status movement.

## Lean identifier proved

```lean
physicalPlaquetteGraph_baseAwareTerminalPredecessorBookkeeping1296
```

Locations:

```text
YangMills/ClayCore/LatticeAnimalCount.lean:4809
YangMills/ClayCore/LatticeAnimalCount.lean:5836
```

## Proof summary

The proof closes:

```lean
PhysicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296
```

by splitting on `k ≤ 1`.

For the low-cardinality branch, it reuses:

```lean
physicalPlaquetteGraph_baseAwareLowCardBookkeepingTotalization1296
```

The safe-deletion clause in the v2.116 bookkeeping interface is vacuous there,
because `2 ≤ k` and `k ≤ 1` are contradictory.  No safe-deletion hypothesis is
invoked for `k < 2`.

For the high-cardinality branch, `2 ≤ k` is available and the proof defines
total functions by classical choice from the existing safe-deletion and
residual-parent APIs:

```lean
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_deletedVertex_has_residualNeighborParent
```

The essential set is exactly the required residual-fiber image:

```lean
((plaquetteGraphPreconnectedSubsetsAnchoredCard
    physicalClayDimension L root k).filter
    (fun X => X.erase (deleted X) = residual)).image parentOf
```

The subset proof follows from the residual-parent membership.  In the singleton
residual subcase, the residual is an anchored bucket of card one, hence contains
only `root`; the chosen parent is therefore `root`, and the existing neighbor
fact becomes the root-shell branch required by v2.116.

The proof does not construct terminal-predecessor menus, terminal-predecessor
codes, or terminal paths.  Those remain isolated in:

```lean
PhysicalPlaquetteGraphResidualTerminalPredecessorDomination1296
```

## Validation

Command run:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result: passed.

The new theorem-specific axiom trace is:

```text
YangMills.physicalPlaquetteGraph_baseAwareTerminalPredecessorBookkeeping1296:
  [propext, Classical.choice, Quot.sound]
```

## Remaining proof burden

The remaining independent blocker for the v2.116 two-input bridge is:

```lean
PhysicalPlaquetteGraphResidualTerminalPredecessorDomination1296
```

Once that theorem closes, the already-proved bridge:

```lean
physicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296_of_baseAwareBookkeeping_of_terminalPredecessorDomination1296
```

can compose the chain forward.  This still does not by itself move `F3-COUNT`;
the strengthened decoder route and constants require Cowork audit.

## Non-claims

This task does not prove:

- `PhysicalPlaquetteGraphResidualTerminalPredecessorDomination1296`;
- `PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296` unconditionally;
- `PhysicalPlaquetteGraphDeletedVertexDecoderStep1296x1296x1296`;
- any compression to the older `1296` or `1296 x 1296` constants.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No ledger status, project percentage,
README metric, planner metric, or Clay-level claim moved.
