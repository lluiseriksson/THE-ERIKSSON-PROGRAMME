# F3 base-aware multi-portal interface v2.95

**Task:** `CODEX-F3-BASEAWARE-MULTIPORTAL-INTERFACE-001`  
**Date:** 2026-04-27  
**Status:** `INTERFACE_AND_BRIDGE_LANDED_NO_MATH_STATUS_MOVE`

## What landed

Codex added the base-aware successor producer interface:

```lean
PhysicalPlaquetteGraphBaseAwareMultiPortalSupportedSafeDeletionOrientation1296x1296
```

The interface is the v2.94 successor to the blocked strict multi-portal
orientation.  It keeps the residual-only portal menu for non-singleton
residuals, but gives singleton residuals a separate root-shell branch.

## Why this handles the k=2 blocker

The v2.93 obstruction was:

```text
residual = {root}
parent = root
portal = root
```

The strict interface then forced:

```lean
root ∈ (plaquetteGraph physicalClayDimension L).neighborFinset root
```

The new interface does not do that.  If `(X.erase (deleted X)).card = 1`, it
requires:

```lean
deleted X ∈ (plaquetteGraph physicalClayDimension L).neighborFinset root
```

This is direct root-shell decoding of the deleted plaquette, not self-adjacency
of the residual root.

For non-singleton residuals, the interface keeps the v2.92 shape:

```text
portal from residual-only menu → parent in portal shell → deleted in parent shell
```

## Bridge

Codex added the no-sorry bridge:

```lean
physicalPlaquetteGraphDeletedVertexDecoderStep1296x1296x1296_of_baseAwareMultiPortalSupportedSafeDeletionOrientation1296x1296
```

The bridge target is exactly:

```lean
PhysicalPlaquetteGraphDeletedVertexDecoderStep1296x1296x1296
```

The reconstruction function branches on `residual.card = 1`:

1. Singleton residual: ignore the first two symbols and decode the deleted
   plaquette from the root shell using the third `Fin 1296` symbol.
2. Non-singleton residual: decode portal, parent, and deleted plaquette using
   the triple-symbol route.

## Validation

Command run:

```bash
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result:

```text
Build completed successfully (8184 jobs).
```

The new bridge has the required canonical axiom trace:

```text
YangMills.physicalPlaquetteGraphDeletedVertexDecoderStep1296x1296x1296_of_baseAwareMultiPortalSupportedSafeDeletionOrientation1296x1296
depends on axioms: [propext, Classical.choice, Quot.sound]
```

The `#print axioms` line is recorded in
`YangMills/ClayCore/LatticeAnimalCount.lean`.

## Non-claims

This is still triple-symbol progress only. It does not prove:

- the base-aware producer theorem itself,
- the old single-symbol `Fin 1296` decoder,
- the older product-symbol `Fin 1296 × Fin 1296` decoder,
- compression from `1296^3` to `1296^2` or `1296`,
- F3-COUNT closure.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No ledger row, project percentage,
README metric, planner metric, or Clay-level claim moves from this task.

## Next audit target

Recommended Cowork audit:

```text
COWORK-AUDIT-CODEX-V2.95-BASEAWARE-BRIDGE-001
```

Audit that the singleton residual branch avoids self-neighbor assumptions, that
the bridge does not compress constants, and that F3-COUNT remains conditional.
