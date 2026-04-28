# F3 base-aware last-step portal image interface v2.101

**Task:** `CODEX-F3-BASEAWARE-LAST-STEP-PORTAL-IMAGE-INTERFACE-001`  
**Date:** 2026-04-27  
**Status:** `INTERFACE_AND_BRIDGE_LANDED_NO_MATH_STATUS_MOVE`

## What landed

Codex added the Lean interface:

```lean
PhysicalPlaquetteGraphBaseAwareResidualLastStepPortalImageBound1296
```

The interface exposes a residual-local selector:

```lean
lastStepPortalOfParent residual p
```

For every essential parent `p`, this selector carries:

1. membership in the residual bucket, and
2. for non-singleton residuals, portal-local adjacency to `p`.

It also asks for the selected portal image:

```lean
(essential residual).attach.image
  (fun p => lastStepPortalOfParent residual p)
```

to have cardinality at most `1296`.

This is the intended sharper burden from v2.100.  It does not bound the raw
residual frontier and does not use root-shell reachability as adjacency.

## Bridge

Codex added the no-sorry bridge:

```lean
physicalPlaquetteGraphBaseAwareResidualPortalMenuBound1296_of_baseAwareResidualLastStepPortalImageBound1296
```

Bridge target:

```lean
PhysicalPlaquetteGraphBaseAwareResidualPortalMenuBound1296
```

The bridge defines:

```lean
portalMenu residual :=
  (essential residual).attach.image
    (fun p => lastStepPortalOfParent residual p)

portalOfParent residual p :=
  lastStepPortalOfParent residual p
```

Then it repacks:

- subset of residual from selector membership,
- `card <= 1296` from the selected-image bound,
- non-singleton portal-local support from selector adjacency,
- the shared base-aware safe-deletion branch from the interface.

## Lean locations

```text
YangMills/ClayCore/LatticeAnimalCount.lean:3134
  PhysicalPlaquetteGraphBaseAwareResidualLastStepPortalImageBound1296

YangMills/ClayCore/LatticeAnimalCount.lean:3245
  physicalPlaquetteGraphBaseAwareResidualPortalMenuBound1296_of_baseAwareResidualLastStepPortalImageBound1296

YangMills/ClayCore/LatticeAnimalCount.lean:5039
  #print axioms physicalPlaquetteGraphBaseAwareResidualPortalMenuBound1296_of_baseAwareResidualLastStepPortalImageBound1296
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
YangMills.physicalPlaquetteGraphBaseAwareResidualPortalMenuBound1296_of_baseAwareResidualLastStepPortalImageBound1296
depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Non-claims

This task does not prove:

- `PhysicalPlaquetteGraphBaseAwareResidualLastStepPortalImageBound1296`,
- `PhysicalPlaquetteGraphBaseAwareResidualPortalMenuBound1296`,
- `PhysicalPlaquetteGraphBaseAwareMultiPortalSupportedSafeDeletionOrientation1296x1296`,
- the triple-symbol decoder from first principles,
- any compression to older constants,
- F3-COUNT closure.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`.  No ledger row, project percentage,
README metric, planner metric, or Clay-level claim moves from this task.

## Next Codex task

Recommended next task:

```text
CODEX-F3-PROVE-BASEAWARE-LAST-STEP-PORTAL-IMAGE-BOUND-001
```

Attempt to prove
`PhysicalPlaquetteGraphBaseAwareResidualLastStepPortalImageBound1296` or reduce
it to the next exact no-closure blocker.  The proof must construct a
residual-local adjacent predecessor selector and prove the selected-image
cardinality bound, without choosing portals post-hoc from `(X, deleted X)`.
