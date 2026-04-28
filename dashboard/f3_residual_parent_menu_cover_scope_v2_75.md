# F3 Residual Parent-Menu Cover Scope v2.75

Timestamp: 2026-04-27T05:20:00Z

Task: `CODEX-F3-RESIDUAL-PARENT-MENU-COVER-SCOPE-001`

## What Landed

Codex formalized the parent-menu cover blocker isolated by v2.74 as a stable
Lean proposition:

```lean
PhysicalPlaquetteGraphResidualParentMenuCovers1296
```

and added the bridge:

```lean
physicalPlaquetteGraphSymbolicResidualParentSelector1296_of_residualParentMenuCovers1296
```

The proposition fixes, for each residual bucket, a residual-only menu:

```lean
Finset (ConcretePlaquette physicalClayDimension L) ->
  Fin 1296 -> Option (ConcretePlaquette physicalClayDimension L)
```

Every current anchored bucket must have at least one safe deleted plaquette whose
residual-neighbor parent appears in that residual-only menu.  This avoids the
post-hoc `(X,z)` parent choice that v2.74 rejected.

## Handoff

The exact handoff to the v2.73 symbolic selector is:

```lean
PhysicalPlaquetteGraphResidualParentMenuCovers1296
  -> PhysicalPlaquetteGraphSymbolicResidualParentSelector1296
```

implemented by:

```lean
physicalPlaquetteGraphSymbolicResidualParentSelector1296_of_residualParentMenuCovers1296
```

Together with v2.73:

```lean
physicalPlaquetteGraphDeletedVertexDecoderStep1296x1296_of_symbolicResidualParentSelector1296
```

this gives the bridge chain:

```text
parent-menu cover
  -> symbolic residual parent selector
  -> strengthened product-symbol deleted-vertex decoder
```

Only the bridge chain is formalized.  The parent-menu cover theorem itself is
still open.

## Validation

Build:

```powershell
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result:

```text
Build completed successfully (8184 jobs).
```

Pinned trace:

```text
YangMills.physicalPlaquetteGraphSymbolicResidualParentSelector1296_of_residualParentMenuCovers1296
depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry`.  No new project axiom.

## Project Status

`F3-COUNT` remains `CONDITIONAL_BRIDGE`.  The old `Fin 1296` decoder contract is
not claimed.  The strengthened `1296^2` route still requires Cowork audit before
any downstream constant, ledger status, or percentage can move.

Recommended next task:

```text
CODEX-F3-PROVE-RESIDUAL-PARENT-MENU-COVER-001
```
