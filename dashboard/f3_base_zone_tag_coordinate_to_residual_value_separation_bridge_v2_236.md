# F3 base-zone tag coordinate to residual-value separation bridge v2.236

Task: `CODEX-F3-BASE-ZONE-TAG-COORDINATE-TO-RESIDUAL-VALUE-SEPARATION-BRIDGE-001`

Status: `DONE_CONDITIONAL_BRIDGE_LANDED_COORDINATE_PREMISE_OPEN`

Timestamp: `2026-04-28T08:55:00Z`

## Lean Addition

Added the no-sorry bridge:

```lean
physicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSeparation1296_of_residualFiberBookkeepingBaseZoneTagCoordinate1296
```

Premise:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296
```

Target:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSeparation1296
```

## Bridge Shape

The proof obtains
`PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinateData` from
the coordinate premise and repacks it into
`PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSeparationData`.

The residual-value code is defined directly from the base-zone tag coordinate:

```lean
residualValueCode residual q :=
  coordinateData.baseZoneTagIntoFin1296 residual
    (coordinateData.baseZoneTagOfResidualValue residual q)
```

The selected-admissible equality-reflection field is exactly:

```lean
coordinateData.selectedAdmissible_injective
```

## Conditionality

This bridge is conditional.  It does not prove:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296
```

The substantive upstream blocker remains the existing coordinate premise,
which the v2.219 attempt records as reducing to:

```lean
PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296
```

and later scope/recovery artifacts refine through the base-zone coordinate
source/realization/certificate lanes.  This bridge only removes the missing
formal repackaging step between the coordinate theorem and v2.234.

## Guardrails

The bridge does not use downstream residual-value realization/source/origin
interfaces in reverse.  It also does not use selected-image cardinality,
bounded menu cardinality, empirical search, `finsetCodeOfCardLe`, root-shell
codes, local-neighbor codes, local-displacement codes, parent-relative
`terminalNeighborCode` equality, deleted-X shortcuts, or the v2.161 cycle.

## Validation

Command:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result: passed.

Focused axiom trace:

```text
YangMills.physicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSeparation1296_of_residualFiberBookkeepingBaseZoneTagCoordinate1296:
  [propext, Classical.choice, Quot.sound]
```

F3-COUNT remains `CONDITIONAL_BRIDGE`.  No status, percentage, README metric,
planner metric, ledger row, proof closure claim, or Clay-level claim moved.

## Next Task

```text
CODEX-F3-PROVE-BASE-ZONE-RESIDUAL-VALUE-CODE-SEPARATION-VIA-TAG-COORDINATE-001
```

Attempt to close `PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSeparation1296`
through the new conditional bridge, or record the exact remaining no-closure
blocker at the coordinate premise.
