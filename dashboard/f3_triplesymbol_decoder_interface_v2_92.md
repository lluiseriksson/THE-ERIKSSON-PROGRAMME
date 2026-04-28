# F3 triple-symbol decoder interface v2.92

**Task:** `CODEX-F3-TRIPLESYMBOL-DECODER-INTERFACE-001`  
**Date:** 2026-04-27  
**Status:** `INTERFACE_AND_BRIDGE_LANDED_NO_MATH_STATUS_MOVE`

## What landed

Codex added a separate triple-symbol decoder contract:

```lean
PhysicalPlaquetteGraphDeletedVertexDecoderStep1296x1296x1296
```

at `YangMills/ClayCore/LatticeAnimalCount.lean:2888`.

The symbol type is:

```lean
Fin 1296 x (Fin 1296 x Fin 1296)
```

It is intentionally distinct from both earlier decoder contracts:

- `PhysicalPlaquetteGraphDeletedVertexDecoderStep1296`
- `PhysicalPlaquetteGraphDeletedVertexDecoderStep1296x1296`

No compression from the triple symbol back to either old constant is claimed.

## Bridge

Codex also added the no-sorry bridge:

```lean
physicalPlaquetteGraphDeletedVertexDecoderStep1296x1296x1296_of_multiPortalSupportedSafeDeletionOrientation1296x1296
```

at `YangMills/ClayCore/LatticeAnimalCount.lean:3069`.

The bridge consumes:

```lean
PhysicalPlaquetteGraphMultiPortalSupportedSafeDeletionOrientation1296x1296
```

and constructs the decoder by using:

1. `portal-code`: selects the residual portal from the residual-only portal menu.
2. `parent-code`: decodes the parent inside the portal-local shell.
3. `deleted-code`: decodes the deleted plaquette inside the parent-local shell.

The local shell decoding uses the existing `physicalNeighborDecodeOfStepCode` machinery and the physical ternary step-code bound.

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
YangMills.physicalPlaquetteGraphDeletedVertexDecoderStep1296x1296x1296_of_multiPortalSupportedSafeDeletionOrientation1296x1296
depends on axioms: [propext, Classical.choice, Quot.sound]
```

The `#print axioms` line is recorded at `YangMills/ClayCore/LatticeAnimalCount.lean:4713`.

## Honesty constraints

This is triple-symbol progress only. It does not prove:

- the old single-symbol `Fin 1296` decoder,
- the older product-symbol `Fin 1296 x Fin 1296` decoder,
- any compression theorem from `1296^3` to `1296^2` or `1296`,
- the multi-portal orientation proposition itself.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No ledger row, project percentage, README metric, planner metric, or Clay-level claim moves from this task.

## Next Lean target

The next Codex task is:

```text
CODEX-F3-PROVE-MULTIPORTAL-ORIENTATION-001
```

Target theorem:

```lean
PhysicalPlaquetteGraphMultiPortalSupportedSafeDeletionOrientation1296x1296
```

If that theorem closes, it may compose only through the v2.92 triple-symbol bridge unless a separate Cowork-audited compression theorem is later proved.
