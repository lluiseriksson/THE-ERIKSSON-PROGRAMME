# F3 base-aware portal-menu bound interface v2.98

**Task:** `CODEX-F3-BASEAWARE-PORTAL-MENU-BOUND-INTERFACE-001`  
**Date:** 2026-04-27  
**Status:** `INTERFACE_AND_BRIDGE_LANDED_NO_MATH_STATUS_MOVE`

## What landed

Codex added the Lean interface:

```lean
PhysicalPlaquetteGraphBaseAwareResidualPortalMenuBound1296
```

This interface factors the v2.95 producer obligation into:

1. base-aware safe-deletion and parent choices, including the singleton
   root-shell branch, and
2. a residual-only non-singleton portal-menu cover for the essential parent
   fibers.

The second item is the remaining mathematical burden.  The interface does not
prove that burden.

## Bridge

Codex added the no-sorry bridge:

```lean
physicalPlaquetteGraphBaseAwareMultiPortalSupportedSafeDeletionOrientation1296x1296_of_baseAwareResidualPortalMenuBound1296
```

The bridge target is exactly:

```lean
PhysicalPlaquetteGraphBaseAwareMultiPortalSupportedSafeDeletionOrientation1296x1296
```

The bridge only repacks the factored data into the v2.95 producer interface. It
does not bridge to the older strict multi-portal proposition and does not claim
compression to the older `Fin 1296` or `Fin 1296 × Fin 1296` decoder constants.

## Lean Locations

```text
YangMills/ClayCore/LatticeAnimalCount.lean:3134
  PhysicalPlaquetteGraphBaseAwareResidualPortalMenuBound1296

YangMills/ClayCore/LatticeAnimalCount.lean:3188
  physicalPlaquetteGraphBaseAwareMultiPortalSupportedSafeDeletionOrientation1296x1296_of_baseAwareResidualPortalMenuBound1296

YangMills/ClayCore/LatticeAnimalCount.lean:4949
  #print axioms physicalPlaquetteGraphBaseAwareMultiPortalSupportedSafeDeletionOrientation1296x1296_of_baseAwareResidualPortalMenuBound1296
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
YangMills.physicalPlaquetteGraphBaseAwareMultiPortalSupportedSafeDeletionOrientation1296x1296_of_baseAwareResidualPortalMenuBound1296
depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Non-claims

This task does not prove:

- `PhysicalPlaquetteGraphBaseAwareResidualPortalMenuBound1296`,
- `PhysicalPlaquetteGraphBaseAwareMultiPortalSupportedSafeDeletionOrientation1296x1296`,
- the triple-symbol deleted-vertex decoder from first principles,
- the old single-symbol `Fin 1296` decoder,
- any compression from `1296^3`,
- F3-COUNT closure.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No ledger row, project percentage,
README metric, planner metric, or Clay-level claim moves from this task.

## Next Codex Task

Recommended next task:

```text
CODEX-F3-PROVE-BASEAWARE-PORTAL-MENU-BOUND-001
```

Attempt to prove `PhysicalPlaquetteGraphBaseAwareResidualPortalMenuBound1296`
or reduce it to the next exact no-closure blocker. The proof attempt must not
choose portals post-hoc from `(X, deleted X)` and must not treat residual size
or raw frontier growth as the local `1296` degree bound.
