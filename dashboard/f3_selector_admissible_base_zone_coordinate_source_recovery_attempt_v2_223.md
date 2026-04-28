# F3 selector-admissible base-zone coordinate source recovery attempt v2.223

Task: `CODEX-F3-PROVE-SELECTOR-ADMISSIBLE-BASE-ZONE-COORDINATE-SOURCE-RECOVERY-001`

Status: `DONE_NO_CLOSURE_BASE_ZONE_COORDINATE_REALIZATION_SEPARATION_MISSING`

## Recovery audit

The stale predecessor task
`CODEX-F3-PROVE-SELECTOR-ADMISSIBLE-BASE-ZONE-COORDINATE-SOURCE-001`
has no explicit completion evidence in `registry/agent_history.jsonl`.  The
history records only dispatch and `CONFIRMED_BUSY` delivery for that task.
The later v2.222 dashboard artifact records the source interface and erasure
bridge landing, but not a proof of
`PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296`.

There is therefore no conflicting completion evidence to preserve, and this
recovery attempt supersedes the stale in-progress lane without duplicating a
Lean proof claim.

## Lean state used

The current Lean file already contains:

- `PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSourceData`
- `PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296`
- `physicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296_of_residualFiberSelectorAdmissibleBaseZoneCoordinateSource1296`

These names provide the v2.222 interface and bridge into
`PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296`.
They do not construct the source data.

## No-closure result

The proof of
`PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296`
cannot be closed from the currently available Lean/dashboard evidence without
introducing a forbidden or missing structural step.

The exact next blocker is a structural realization/separation theorem,
tentatively:

`PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296`

Expected bridge:

`physicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296_of_baseZoneCoordinateRealizationSeparation1296`

This upstream theorem must provide, for each v2.121 bookkeeping residual fiber:

- a selector-independent residual bookkeeping/base-zone coordinate realization
  relation on the whole residual subtype;
- proof-relevant coordinate certificates for residual values before any fixed
  selector image or bounded menu is supplied;
- an encoding into `Fin 1296`;
- selected-admissible injectivity for residual values carrying
  `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` evidence
  from essential parents.

The existing candidate inventory shows that v2.121 bookkeeping, terminal-neighbor
selector data, and the v2.222 interface do not supply this realization layer.
Using the interface itself as evidence would be circular.

## Rejected routes

This recovery did not use selected-image cardinality, bounded menu cardinality,
empirical bounded search, `finsetCodeOfCardLe`, root-shell codes,
local-neighbor codes, local-displacement codes, parent-relative
`terminalNeighborCode` equality, the deleted-X shortcut, or the v2.161 cycle.

No Lean file was edited, so no `lake build` was required for this recovery
attempt.  F3-COUNT remains `CONDITIONAL_BRIDGE`; no status, percentage, README
metric, planner metric, ledger row, proof claim, or Clay-level claim moved.

## Next task

`CODEX-F3-BASE-ZONE-COORDINATE-REALIZATION-SEPARATION-SCOPE-001`
