# F3 low-cardinality bookkeeping totalization interface v2.119

**Task:** `CODEX-F3-LOWCARD-BOOKKEEPING-TOTALIZATION-INTERFACE-001`  
**Date:** 2026-04-27  
**Status:** Lean interface landed; no F3-COUNT status movement.

## Lean identifiers landed

```lean
PhysicalPlaquetteGraphRootHasDistinctPlaquette
```

Location:

```text
YangMills/ClayCore/LatticeAnimalCount.lean:3422
```

This is a narrow Prop for the uniform non-root fallback needed by the
low-cardinality bookkeeping branch:

```lean
∀ root, ∃ fallbackDeleted, fallbackDeleted ≠ root
```

It is deliberately an interface, not an axiom and not a theorem.  A later task
must prove it from the concrete physical plaquette representation.

```lean
PhysicalPlaquetteGraphBaseAwareLowCardBookkeepingTotalization1296
```

Location:

```text
YangMills/ClayCore/LatticeAnimalCount.lean:3440
```

This interface isolates the `k ≤ 1` image/subset totalization branch needed by:

```lean
PhysicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296
```

It asks for:

- a non-root `fallbackDeleted`;
- total `deleted`, `parentOf`, and `essential`;
- explicit low-card defaults `deleted X = fallbackDeleted` and `parentOf X = root`;
- the load-bearing parent-in-residual clause:

```lean
parentOf X ∈ X.erase (deleted X)
```

for every current anchored bucket in the `k ≤ 1` family;

- the same residual-fiber image identity used by v2.116;
- the resulting `essential residual ⊆ residual` clause.

The interface does not invoke safe deletion and does not rely on an arbitrary
default that bypasses the low-cardinality proof obligation.

## Bridge target

The bridge back into the existing bookkeeping theorem remains:

```lean
PhysicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296
```

The intended proof route is:

1. Split on `k ≤ 1`.
2. Use `PhysicalPlaquetteGraphBaseAwareLowCardBookkeepingTotalization1296` for
   the low-cardinality image/subset branch.
3. Use existing safe-deletion and residual-parent APIs for `2 ≤ k`.
4. Keep the v2.116 downstream bridge unchanged:

```lean
physicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296_of_baseAwareBookkeeping_of_terminalPredecessorDomination1296
```

## Validation

Command run:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result: passed.

No new theorem was added, so no new theorem-specific `#print axioms` trace was
required.  The new declarations are Prop interfaces only.

## Remaining proof burden

The next task is to prove or precisely fail:

```lean
PhysicalPlaquetteGraphRootHasDistinctPlaquette
```

and then use it with:

```lean
plaquetteGraphPreconnectedSubsetsAnchoredCard_zero_eq_empty
plaquetteGraphPreconnectedSubsetsAnchoredCard_one_subset_singleton
```

to prove:

```lean
PhysicalPlaquetteGraphBaseAwareLowCardBookkeepingTotalization1296
```

## Non-claims

This task does not prove:

- `PhysicalPlaquetteGraphRootHasDistinctPlaquette`;
- `PhysicalPlaquetteGraphBaseAwareLowCardBookkeepingTotalization1296`;
- `PhysicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296`;
- `PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296`;
- any decoder compression to an older constant.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No ledger status, project percentage,
README metric, planner metric, or Clay-level claim moved.
