# F3 terminal-neighbor ambient bookkeeping-tag code interface v2.176

Task: `CODEX-F3-TERMINAL-NEIGHBOR-AMBIENT-BOOKKEEPING-TAG-CODE-INTERFACE-001`

Status: `DONE_INTERFACE_AND_BRIDGE_LANDED_NO_STATUS_MOVE`

## Lean landing

Added the no-sorry Lean interface:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCode1296
```

with supporting data:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCodeData
```

and the projection bridge:

```lean
physicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCode1296_of_residualFiberTerminalNeighborAmbientBookkeepingTagCode1296
```

Bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCode1296
```

## Interface burden

The interface uses the v2.121-style residual-fiber hypotheses and supplies:

- residual-local `terminalNeighborOfParent` selector data;
- `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`;
- a bookkeeping-tag code
  `{q : ConcretePlaquette physicalClayDimension L // q ∈ residual} → Fin 1296`;
- selected-value separation for the chosen terminal-neighbor values.

This is narrower than the v2.173 ambient interface because the bridge packages
the code with:

```lean
ambientOrigin :=
  PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientCodeOrigin.bookkeepingTag
```

## Bridge behavior

The bridge only repacks:

1. the selector;
2. selector evidence;
3. the bookkeeping-tag residual-value code;
4. the selected-value separation theorem.

It sets `ambientOrigin = bookkeepingTag` and reuses the bookkeeping-tag code as
the ambient residual-value code.

## Explicit non-routes

The interface is not selected-image cardinality, not local displacement coding,
not parent-relative `terminalNeighborCode` equality, not empirical search, not
`finsetCodeOfCardLe` on an already bounded selected image, and not the v2.161
cycle through selector-image bounds, code separation, dominating menus, or image
compression.

## Validation

- `lake build YangMills.ClayCore.LatticeAnimalCount` passed.
- `#print axioms physicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCode1296_of_residualFiberTerminalNeighborAmbientBookkeepingTagCode1296`
  reports exactly `[propext, Classical.choice, Quot.sound]`.
- F3-COUNT remains `CONDITIONAL_BRIDGE`; no percentage, status, README metric,
  planner metric, ledger row, or Clay-level claim moved.

## Next Codex task

`CODEX-F3-PROVE-TERMINAL-NEIGHBOR-AMBIENT-BOOKKEEPING-TAG-CODE-001`

Prove `PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCode1296`
or reduce it to the next exact no-closure blocker.
