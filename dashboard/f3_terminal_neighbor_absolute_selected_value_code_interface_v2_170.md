# F3 terminal-neighbor absolute selected-value code interface v2.170

Task: `CODEX-F3-ABSOLUTE-SELECTED-VALUE-CODE-INTERFACE-RETRY-002`

Status: `DONE_INTERFACE_AND_BRIDGE_LANDED_NO_STATUS_MOVE`

## Lean landing

Added the no-sorry Lean interface:

- `PhysicalPlaquetteGraphResidualFiberTerminalNeighborAbsoluteSelectedValueCode1296`

and the projection bridge:

- `physicalPlaquetteGraphResidualFiberTerminalNeighborBasepointIndependentCode1296_of_residualFiberTerminalNeighborAbsoluteSelectedValueCode1296`

Bridge target:

- `PhysicalPlaquetteGraphResidualFiberTerminalNeighborBasepointIndependentCode1296`

## Interface burden

The interface supplies residual-local `terminalNeighborOfParent` selector data,
the existing `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`,
and an absolute residual-value code
`{q : ConcretePlaquette physicalClayDimension L // q ∈ residual} → Fin 1296`.
The separation clause states that equality of the absolute code on selected
terminal-neighbor values forces equality of those selected terminal-neighbor
plaquettes across essential parents in the same residual fiber.

## Explicit non-routes

This interface is not a local displacement code, not parent-relative
`terminalNeighborCode` equality, not local degree, not residual path/root-shell
reachability, not residual size, not raw frontier size, not deleted-vertex
adjacency, not empirical search, not packing/projection of an already bounded
menu, not `finsetCodeOfCardLe` on an already bounded selected image, and not
the v2.161 circular chain.

## Validation

- `lake build YangMills.ClayCore.LatticeAnimalCount` passed.
- `#print axioms physicalPlaquetteGraphResidualFiberTerminalNeighborBasepointIndependentCode1296_of_residualFiberTerminalNeighborAbsoluteSelectedValueCode1296`
  reports exactly `[propext, Classical.choice, Quot.sound]`.
- F3-COUNT remains `CONDITIONAL_BRIDGE`; no percentage, status, README metric,
  planner metric, ledger row, or Clay-level claim moved.
