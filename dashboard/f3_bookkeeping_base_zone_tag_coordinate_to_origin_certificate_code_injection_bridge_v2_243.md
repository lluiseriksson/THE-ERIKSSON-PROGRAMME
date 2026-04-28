# F3 v2.243: Bookkeeping Base-Zone Tag Coordinate to Origin Certificate Code Injection Bridge

Task: `CODEX-F3-BOOKKEEPING-BASE-ZONE-TAG-COORDINATE-TO-ORIGIN-CERTIFICATE-CODE-INJECTION-BRIDGE-001`

Status: `DONE_CONDITIONAL_BRIDGE_LANDED_TAG_COORDINATE_PREMISE_OPEN`

Timestamp: `2026-04-28T15:40:00Z`

## Lean Addition

Added the no-sorry bridge:

```lean
physicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296_of_residualFiberBookkeepingBaseZoneTagCoordinate1296
```

Premise:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296
```

Target:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296
```

## Bridge Shape

The bridge obtains
`PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinateData` from
the tag-coordinate premise and repacks it directly into
`PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjectionData`.

The origin-certificate code is the composed whole-residual `Fin 1296` code:

```lean
baseZoneOriginCertificateCode residual q :=
  coordinateData.baseZoneTagIntoFin1296 residual
    (coordinateData.baseZoneTagOfResidualValue residual q)
```

The selected-admissible equality-reflection field is reused unchanged:

```lean
coordinateData.selectedAdmissible_injective
```

## Conditionality

This bridge is conditional. It does not prove:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296
```

The upstream no-closure blocker remains the tag-coordinate premise recorded in
v2.219, ultimately requiring a non-circular source for:

```lean
PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296
```

The bridge only removes the formal repackaging gap from the tag-coordinate
carrier into the v2.228 origin-certificate code-injection interface.

## Guardrails

The proof does not route through downstream residual-value source, realization,
origin, or separation interfaces in reverse. It does not use selected-image
cardinality, bounded menu cardinality, empirical search, `finsetCodeOfCardLe`,
root-shell/local-neighbor/local-displacement codes, parent-relative
`terminalNeighborCode` equality, deleted-X shortcuts, or the v2.161 cycle.

## Validation

Command:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result: passed.

Focused axiom trace:

```text
YangMills.physicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296_of_residualFiberBookkeepingBaseZoneTagCoordinate1296:
  [propext, Classical.choice, Quot.sound]
```

F3-COUNT remains `CONDITIONAL_BRIDGE`. No status, percentage, README metric,
planner metric, ledger row, proof closure claim, or Clay-level claim moved.

## Next Task

```text
CODEX-F3-PROVE-BASE-ZONE-ORIGIN-CERTIFICATE-CODE-INJECTION-VIA-TAG-COORDINATE-001
```

Attempt to close
`PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296`
through the new conditional bridge, or record the exact remaining no-closure
blocker at the tag-coordinate premise without treating the bridge as proof of
that premise.
