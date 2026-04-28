# F3 bookkeeping tag space injection interface v2.213

Task: `CODEX-F3-BOOKKEEPING-TAG-SPACE-INJECTION-INTERFACE-001`

Status: `DONE_INTERFACE_AND_BRIDGE_LANDED_NO_STATUS_MOVE`

## Lean landing

Added no-sorry interface:

- `PhysicalPlaquetteGraphResidualFiberBookkeepingTagSpaceInjection1296`
- Location: `YangMills/ClayCore/LatticeAnimalCount.lean:4090`

Added no-sorry bridge:

- `physicalPlaquetteGraphResidualFiberSelectorAdmissibleBookkeepingTagInjection1296_of_residualFiberBookkeepingTagSpaceInjection1296`
- Location: `YangMills/ClayCore/LatticeAnimalCount.lean:4221`
- Bridge target: `PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBookkeepingTagInjection1296`

The new interface exposes, for each v2.121 bookkeeping residual fiber:

- a residual-indexed bookkeeping/base-zone tag space,
- a residual-value tag extractor on the whole residual subtype,
- an encoding from that tag space into `Fin 1296`,
- selected-admissible tag injectivity for residual values carrying
  `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` evidence from
  essential parents.

The bridge composes the residual-value tag extractor with the `Fin 1296`
encoding to build
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCodeData`,
then passes the selected-admissible separation law through unchanged.

## Non-routes

This interface and bridge do not use selected-image cardinality, bounded menu
cardinality, empirical search, `finsetCodeOfCardLe`, root-shell codes, local
neighbor codes, local displacement codes, parent-relative `terminalNeighborCode`
equality, deleted-vertex adjacency outside the residual, deleted `X` as a
residual terminal neighbor for `residual = X.erase (deleted X)`, or the v2.161
selector-image circular chain.

## Validation

- `lake build YangMills.ClayCore.LatticeAnimalCount` passed.
- `#print axioms PhysicalPlaquetteGraphResidualFiberBookkeepingTagSpaceInjection1296`
  reports `[propext, Classical.choice, Quot.sound]`.
- `#print axioms physicalPlaquetteGraphResidualFiberSelectorAdmissibleBookkeepingTagInjection1296_of_residualFiberBookkeepingTagSpaceInjection1296`
  reports `[propext, Classical.choice, Quot.sound]`.

## Next task

`CODEX-F3-PROVE-BOOKKEEPING-TAG-SPACE-INJECTION-001` should prove
`PhysicalPlaquetteGraphResidualFiberBookkeepingTagSpaceInjection1296` or reduce
it to the next exact no-closure blocker.

F3-COUNT remains `CONDITIONAL_BRIDGE`; no status, percentage, README metric,
planner metric, ledger row, vacuity caveat, proof claim, or Clay-level claim
moved.
