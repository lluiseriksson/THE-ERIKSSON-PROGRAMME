# F3 base-aware canonical last-edge predecessor interface v2.107

**Task:** `CODEX-F3-BASEAWARE-CANONICAL-LAST-EDGE-PREDECESSOR-INTERFACE-001`  
**Date:** 2026-04-27  
**Status:** `INTERFACE_AND_BRIDGE_LANDED_NO_MATH_STATUS_MOVE`

## What landed

Codex added the Lean data structure:

```lean
PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgeData
```

and the Lean interface:

```lean
PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgePredecessorSelector1296
```

The new data structure carries, for each residual bucket and target essential
parent:

1. a residual endpoint `target`,
2. a proof that `target.1` is the target parent,
3. a selected residual predecessor,
4. an induced residual walk from the predecessor to the target,
5. a `Fin 1296` code.

This is the extra path/last-edge factorization missing from v2.104.  It is not a
plain restatement of
`PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastStepPredecessorImageBound1296`.

## Bridge

Codex added the no-sorry bridge:

```lean
physicalPlaquetteGraphBaseAwareResidualCanonicalLastStepPredecessorImageBound1296_of_baseAwareResidualCanonicalLastEdgePredecessorSelector1296
```

Bridge target:

```lean
PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastStepPredecessorImageBound1296
```

The bridge defines the v2.104 predecessor-code pair by projecting:

```lean
((canonicalLastEdgeData residual p).predecessor,
  (canonicalLastEdgeData residual p).code)
```

and repacks:

- the shared base-aware safe-deletion branch,
- residual-fiber image equality,
- last-edge adjacency,
- `Fin 1296` code separation,
- selected predecessor image bound.

The bridge does not construct the canonical last-edge selector itself and does
not prove the selected-image bound.  Those are still the next mathematical
targets.

## Lean locations

```text
YangMills/ClayCore/LatticeAnimalCount.lean:3261
  PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgeData

YangMills/ClayCore/LatticeAnimalCount.lean:3282
  PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgePredecessorSelector1296

YangMills/ClayCore/LatticeAnimalCount.lean:3461
  physicalPlaquetteGraphBaseAwareResidualCanonicalLastStepPredecessorImageBound1296_of_baseAwareResidualCanonicalLastEdgePredecessorSelector1296

YangMills/ClayCore/LatticeAnimalCount.lean:5250
  #print axioms physicalPlaquetteGraphBaseAwareResidualCanonicalLastStepPredecessorImageBound1296_of_baseAwareResidualCanonicalLastEdgePredecessorSelector1296
```

## Validation

Command run:

```bash
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result:

```text
Build completed successfully (8184 jobs).
```

The new bridge has the canonical axiom trace:

```text
YangMills.physicalPlaquetteGraphBaseAwareResidualCanonicalLastStepPredecessorImageBound1296_of_baseAwareResidualCanonicalLastEdgePredecessorSelector1296
depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Non-claims

This task does not prove:

- `PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgePredecessorSelector1296`,
- `PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastStepPredecessorImageBound1296`,
- `PhysicalPlaquetteGraphBaseAwareResidualLastStepPortalImageBound1296`,
- `PhysicalPlaquetteGraphBaseAwareResidualPortalMenuBound1296`,
- `PhysicalPlaquetteGraphBaseAwareMultiPortalSupportedSafeDeletionOrientation1296x1296`,
- `PhysicalPlaquetteGraphDeletedVertexDecoderStep1296x1296x1296`,
- any compression to older constants,
- F3-COUNT closure.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`.  No ledger row, project percentage,
README metric, planner metric, or Clay-level claim moves from this task.

## Recommended next task

```text
CODEX-F3-PROVE-BASEAWARE-CANONICAL-LAST-EDGE-PREDECESSOR-SELECTOR-001
```

Attempt to prove
`PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgePredecessorSelector1296`
or reduce it to the next exact no-closure blocker.
