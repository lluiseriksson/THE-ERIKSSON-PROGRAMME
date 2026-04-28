# F3 base-zone coordinate realization separation interface v2.224

Task: `CODEX-F3-BASE-ZONE-COORDINATE-REALIZATION-SEPARATION-INTERFACE-001`

Status: `DONE_INTERFACE_AND_BRIDGE_LANDED`

Date: 2026-04-28T02:30:00Z

## Lean additions

Added the proof-relevant origin/certificate carrier:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparationData
```

Added the no-sorry Prop/interface:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296
```

Added the erasure bridge:

```lean
physicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296_of_baseZoneCoordinateRealizationSeparation1296
```

The bridge target is exactly:

```lean
PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296
```

## Interface shape

The new interface is not merely a restatement of
`PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296`.
It inserts an origin/certificate layer:

```lean
baseZoneCoordinateOrigin
baseZoneCoordinateOfOrigin
baseZoneCoordinateOrigin_realizes
baseZoneCoordinateOriginOfResidualValue
selectorAdmissible_origin_injective
```

The bridge erases each origin certificate into the v2.222
`baseZoneCoordinateRealizes` relation and applies
`selectorAdmissible_origin_injective` to prove the realized-coordinate
injectivity required by
`PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSourceData`.

## Rejected routes

The interface and bridge do not use selected-image cardinality, bounded menu
cardinality, empirical search, `finsetCodeOfCardLe`, root-shell codes,
local-neighbor codes, local-displacement codes, parent-relative
`terminalNeighborCode` equality, the deleted-X shortcut for
`residual = X.erase (deleted X)`, or the v2.161 selector-image cycle.

## Validation

Command:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result: passed.

New theorem/interface axiom traces:

```text
PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparationData:
  [propext, Classical.choice, Quot.sound]

PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296:
  [propext, Classical.choice, Quot.sound]

physicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296_of_baseZoneCoordinateRealizationSeparation1296:
  [propext, Classical.choice, Quot.sound]
```

F3-COUNT remains `CONDITIONAL_BRIDGE`.  No status, percentage, README metric,
planner metric, ledger row, proof claim beyond the Lean interface/bridge, or
Clay-level claim moved.

## Next task

```text
CODEX-F3-PROVE-BASE-ZONE-COORDINATE-REALIZATION-SEPARATION-001
```

Prove `PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296`
or reduce it to the next exact no-closure blocker.
