# F3 terminal-neighbor ambient value code interface v2.173

Task: `CODEX-F3-TERMINAL-NEIGHBOR-AMBIENT-VALUE-CODE-INTERFACE-001`

Status: `DONE_INTERFACE_AND_BRIDGE_LANDED_NO_STATUS_MOVE`

## Lean landing

Added the no-sorry Lean interface:

- `PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCode1296`

with supporting data:

- `PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientCodeOrigin`
- `PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCodeData`

and the projection bridge:

- `physicalPlaquetteGraphResidualFiberTerminalNeighborAbsoluteSelectedValueCode1296_of_residualFiberTerminalNeighborAmbientValueCode1296`

Bridge target:

- `PhysicalPlaquetteGraphResidualFiberTerminalNeighborAbsoluteSelectedValueCode1296`

## Interface burden

The interface supplies residual-local `terminalNeighborOfParent` selector data,
the existing `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`,
and an ambient residual-value code

```lean
{q : ConcretePlaquette physicalClayDimension L // q ∈ residual} → Fin 1296
```

packaged in `PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCodeData`.
Each residual code carries an `ambientOrigin` tag:

- `baseZoneEnumeration`
- `bookkeepingTag`
- `canonicalLastEdgeFrontier`

The separation clause states that equality of this ambient code on selected
terminal-neighbor values forces equality of those selected terminal-neighbor
plaquettes across essential parents in the same residual fiber.

## Bridge behavior

The bridge is only a direct projection into v2.170:

1. unpack the ambient selector, selector evidence, ambient code data, and
   selected-value separation;
2. forget the `ambientOrigin` tag;
3. reuse `(ambientValueCodeData residual).ambientValueCode` as the v2.170
   absolute residual-value code.

It does not construct a code from selected-image cardinality and does not pass
through selector-image compression or menu bounds.

## Explicit non-routes

This interface is not a local displacement code, not parent-relative
`terminalNeighborCode` equality, not selected-image cardinality, not
selected-image packing/projection, not `finsetCodeOfCardLe` on an already
bounded selected image, not empirical search, not local degree, residual paths,
root-shell reachability, residual size, raw frontier, deleted-vertex adjacency,
or the v2.161 circular chain.

## Validation

- `lake build YangMills.ClayCore.LatticeAnimalCount` passed.
- `#print axioms physicalPlaquetteGraphResidualFiberTerminalNeighborAbsoluteSelectedValueCode1296_of_residualFiberTerminalNeighborAmbientValueCode1296`
  reports exactly `[propext, Classical.choice, Quot.sound]`.
- F3-COUNT remains `CONDITIONAL_BRIDGE`; no percentage, status, README metric,
  planner metric, ledger row, or Clay-level claim moved.

## Next Codex task

`CODEX-F3-PROVE-TERMINAL-NEIGHBOR-AMBIENT-VALUE-CODE-001`

Prove `PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCode1296`
or reduce it to the next exact no-closure blocker.
