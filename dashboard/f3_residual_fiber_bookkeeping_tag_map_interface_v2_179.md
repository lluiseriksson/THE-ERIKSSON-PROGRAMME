# F3 residual-fiber bookkeeping tag map interface v2.179

Task: `CODEX-F3-RESIDUAL-FIBER-BOOKKEEPING-TAG-MAP-INTERFACE-001`

Status: `DONE_INTERFACE_AND_BRIDGE_LANDED_NO_STATUS_MOVE`

## Lean landing

Added the no-sorry Lean interface:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagMap1296
```

and the repacking bridge:

```lean
physicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCode1296_of_residualFiberBookkeepingTagMap1296
```

Bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCode1296
```

## Interface burden

The interface uses the same v2.121 bookkeeping residual-fiber hypotheses as the
bookkeeping-tag terminal-neighbor interface and exposes:

- a residual-local `terminalNeighborOfParent` selector;
- `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`;
- a bookkeeping residual-value tag map

```lean
∀ residual,
  {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} →
    Fin 1296
```

- selected-value separation for terminal-neighbor selections in each residual
  fiber.

The tag map lives on the whole residual subtype before the selected
terminal-neighbor image is considered.  It is therefore not manufactured from
selected-image cardinality.

## Bridge behavior

The bridge only repacks the direct residual-value tag map as:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCodeData
```

and reuses the selector, selector evidence, and selected-value separation
clause.  It does not derive a code from cardinality and does not use
`finsetCodeOfCardLe`.

## Explicit non-routes

The interface is not selected-image cardinality, not local displacement coding,
not parent-relative `terminalNeighborCode` equality, not empirical search, not
`finsetCodeOfCardLe` on an already bounded selected image, and not the v2.161
cycle through selector-image bounds, code separation, dominating menus, or image
compression.

## Validation

- `lake build YangMills.ClayCore.LatticeAnimalCount` passed.
- `#print axioms physicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCode1296_of_residualFiberBookkeepingTagMap1296`
  reports exactly `[propext, Classical.choice, Quot.sound]`.
- F3-COUNT remains `CONDITIONAL_BRIDGE`; no percentage, status, README metric,
  planner metric, ledger row, or Clay-level claim moved.

## Next Codex task

`CODEX-F3-PROVE-RESIDUAL-FIBER-BOOKKEEPING-TAG-MAP-001`

Prove `PhysicalPlaquetteGraphResidualFiberBookkeepingTagMap1296` or reduce it
to the next exact no-closure blocker.
