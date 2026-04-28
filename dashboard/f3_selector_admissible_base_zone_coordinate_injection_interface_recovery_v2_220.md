# F3 selector-admissible base-zone coordinate injection interface recovery v2.220

Task:
`CODEX-F3-SELECTOR-ADMISSIBLE-BASE-ZONE-COORDINATE-INJECTION-INTERFACE-RECOVERY-001`

Status: `DONE_INTERFACE_AND_BRIDGE_RECOVERED`

Date: 2026-04-28T00:32:00Z

## Recovery result

The stale original interface task had registry status `DONE`, but no explicit
`completed_at`, artifact, or Lean target was present.  This recovery therefore
landed the missing Lean interface directly rather than normalizing a completed
artifact.

## Lean additions

Added the source-facing carrier:

```lean
PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjectionData
```

Added the no-sorry Prop/interface:

```lean
PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296
```

Added the bridge:

```lean
physicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296_of_residualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296
```

The bridge target is exactly:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296
```

## Interface shape

The new source carrier exposes selector-independent residual
bookkeeping/base-zone coordinate data on the whole residual subtype:

- `baseZoneCoordinateSpace`;
- `baseZoneCoordinateOfResidualValue`;
- `baseZoneCoordinateIntoFin1296`;
- `selectorAdmissible_injective`.

The bridge is structural repackaging into the v2.218 downstream carrier
`PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinateData`.

## Rejected routes

The interface and bridge do not use selected-image cardinality, bounded menu
cardinality, empirical search, `finsetCodeOfCardLe`,
root-shell/local-neighbor/local-displacement codes as residual-subtype
bookkeeping tag injectivity, parent-relative `terminalNeighborCode` equality,
the deleted-X shortcut for `residual = X.erase (deleted X)`, or the v2.161
selector-image cycle.

## Validation

Command:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result: passed.

New theorem/interface axiom traces:

```text
PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjectionData:
  [propext, Classical.choice, Quot.sound]

PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296:
  [propext, Classical.choice, Quot.sound]

physicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296_of_residualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296:
  [propext, Classical.choice, Quot.sound]
```

F3-COUNT remains `CONDITIONAL_BRIDGE`.  No status, percentage, README metric,
planner metric, ledger row, proof claim beyond the Lean interface/bridge, or
Clay-level claim moved.

## Next task

```text
CODEX-F3-PROVE-SELECTOR-ADMISSIBLE-BASE-ZONE-COORDINATE-INJECTION-001
```

Prove
`PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296`
or reduce it to the next exact no-closure blocker.
