# F3 v2.253: Base-Zone Coordinate Realization/Separation Premise Recheck

Task: `CODEX-F3-BASE-ZONE-COORDINATE-REALIZATION-SEPARATION-PREMISE-RECHECK-AFTER-V2-252-001`

Status: `DONE_NO_CLOSURE_BASE_ZONE_ORIGIN_CERTIFICATE_SOURCE_STILL_MISSING`

Timestamp: `2026-04-28T16:34:22Z`

## Checked Target

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296
```

The direct Lean bridge into this target remains:

```lean
physicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296_of_baseZoneOriginCertificateSource1296
```

Bridge direction:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296
  -> PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296
```

## Candidate Sources Checked

| Candidate | Direction | Result |
| --- | --- | --- |
| `PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296` | Upstream into realization/separation | Valid conditional bridge, but premise still open |
| `PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296` | Upstream into origin-certificate source, not directly into realization/separation | Context only; v2.248/v2.249 did not close it |
| `PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296` | Conditional route into code injection | Rejected as closure evidence because the tag-coordinate premise remains open |
| `PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296` | Downstream from realization/separation | Rejected as reverse evidence |
| Coordinate injection, residual-value source/realization/origin/separation interfaces | Downstream/conditional in the current chain | Rejected as reverse evidence |

## Result

No non-circular proof of the base-zone coordinate realization/separation
premise is available after v2.252. The available Lean bridge is still
conditional on selector-independent base-zone origin/certificate source data
and does not construct that source.

The exact immediate no-closure blocker remains:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296
```

## Upstream Chain

The next Lean bridge is:

```lean
physicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296_of_baseZoneOriginCertificateCodeInjection1296
```

with direction:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296
  -> PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296
```

The v2.248 recheck records that the origin-certificate source target remains
blocked at:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296
```

and v2.249 records the tag-coordinate route to code injection as conditional on:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296
```

Those facts are upstream context only. This v2.253 recheck does not claim
closure of any upstream premise.

## Downstream Routes Rejected

The following route was not used as proof of the realization/separation
premise:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296
  -> PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296
  -> PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296
  -> PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296
```

Nor were downstream origin-certificate, residual-value, or separation
interfaces used in reverse to prove the realization/separation premise.

## Guardrails

This recheck does not route through downstream residual-value realization,
source, origin, or separation interfaces in reverse. It does not use
selected-image cardinality, bounded menu cardinality, empirical search,
`finsetCodeOfCardLe`, root-shell/local-neighbor/local-displacement codes,
parent-relative `terminalNeighborCode` equality, deleted-X shortcuts, or the
v2.161 cycle.

## Validation

No Lean file was edited, so no `lake build` was required. No new theorem or
theorem-specific axiom trace was introduced.

F3-COUNT remains `CONDITIONAL_BRIDGE`. No status, percentage, README metric,
planner metric, ledger row, proof closure claim, or Clay-level claim moved.

## Next Task

```text
CODEX-F3-BASE-ZONE-ORIGIN-CERTIFICATE-SOURCE-PREMISE-RECHECK-AFTER-V2-253-001
```

Recheck whether a non-circular source now proves
`PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296` after
v2.253. Do not treat downstream realization/separation, coordinate source,
coordinate injection, tag-coordinate, residual-value, or separation interfaces
as proof of that premise.
