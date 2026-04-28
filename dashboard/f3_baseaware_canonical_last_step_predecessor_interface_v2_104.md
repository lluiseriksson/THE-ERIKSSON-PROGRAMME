# F3 base-aware canonical last-step predecessor interface v2.104

**Task:** `CODEX-F3-BASEAWARE-CANONICAL-LAST-STEP-PREDECESSOR-INTERFACE-001`  
**Date:** 2026-04-27  
**Status:** `INTERFACE_AND_BRIDGE_LANDED_NO_MATH_STATUS_MOVE`

## What landed

Codex added the Lean interface:

```lean
PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastStepPredecessorImageBound1296
```

The interface extends the v2.101 last-step portal route with explicit canonical
predecessor data:

```lean
canonicalLastStepPredecessor residual p :
  {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} × Fin 1296
```

This separates:

1. the selected predecessor `q`,
2. its membership proof `q ∈ residual`,
3. a `Fin 1296` code for future selected-image compression,
4. a code-separation condition saying equal codes force equal selected
   predecessors.

It is therefore not a simple restatement of
`PhysicalPlaquetteGraphBaseAwareResidualLastStepPortalImageBound1296`.

## Bridge

Codex added the no-sorry bridge:

```lean
physicalPlaquetteGraphBaseAwareResidualLastStepPortalImageBound1296_of_baseAwareResidualCanonicalLastStepPredecessorImageBound1296
```

Bridge target:

```lean
PhysicalPlaquetteGraphBaseAwareResidualLastStepPortalImageBound1296
```

The bridge defines:

```lean
lastStepPortalOfParent residual p :=
  (canonicalLastStepPredecessor residual p).1.1
```

and repacks:

- residual membership from the subtype predecessor,
- non-singleton adjacency from the interface,
- selected-image cardinality from the interface,
- the shared base-aware safe-deletion branch.

The bridge does not prove the selected-image cardinality bound from the `Fin
1296` code.  That remains the next mathematical target.

## Lean locations

```text
YangMills/ClayCore/LatticeAnimalCount.lean:3193
  PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastStepPredecessorImageBound1296

YangMills/ClayCore/LatticeAnimalCount.lean:3344
  physicalPlaquetteGraphBaseAwareResidualLastStepPortalImageBound1296_of_baseAwareResidualCanonicalLastStepPredecessorImageBound1296

YangMills/ClayCore/LatticeAnimalCount.lean:5131
  #print axioms physicalPlaquetteGraphBaseAwareResidualLastStepPortalImageBound1296_of_baseAwareResidualCanonicalLastStepPredecessorImageBound1296
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
YangMills.physicalPlaquetteGraphBaseAwareResidualLastStepPortalImageBound1296_of_baseAwareResidualCanonicalLastStepPredecessorImageBound1296
depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Non-claims

This task does not prove:

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
CODEX-F3-PROVE-BASEAWARE-CANONICAL-LAST-STEP-PREDECESSOR-IMAGE-BOUND-001
```

Attempt to prove
`PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastStepPredecessorImageBound1296`
or reduce it to the next exact no-closure blocker.  The proof should try to
construct the coded predecessor policy and derive the selected predecessor image
bound honestly.
