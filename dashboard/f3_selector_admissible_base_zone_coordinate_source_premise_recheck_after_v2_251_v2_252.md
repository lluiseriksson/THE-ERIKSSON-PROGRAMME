# F3 v2.252: Selector-Admissible Base-Zone Coordinate Source Premise Recheck

Task: `CODEX-F3-SELECTOR-ADMISSIBLE-BASE-ZONE-COORDINATE-SOURCE-PREMISE-RECHECK-AFTER-V2-251-001`

Status: `DONE_NO_CLOSURE_BASE_ZONE_COORDINATE_REALIZATION_SEPARATION_STILL_MISSING`

Timestamp: `2026-04-28T16:28:38Z`

## Checked Target

```lean
PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296
```

The direct Lean bridge into this target remains:

```lean
physicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296_of_baseZoneCoordinateRealizationSeparation1296
```

Bridge direction:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296
  -> PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296
```

## Candidate Sources Checked

| Candidate | Direction | Result |
| --- | --- | --- |
| `PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296` | Upstream into coordinate source | Valid conditional bridge, but premise still open |
| `PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296` | Downstream from coordinate source | Rejected as reverse evidence |
| `PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296` | Further downstream through coordinate injection | Rejected as reverse evidence |
| `PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296` | Upstream into realization/separation, not directly into coordinate source | Context only; v2.248 did not close it |
| Origin-certificate/residual-value code-injection or source interfaces | Downstream/conditional in the current chain | Rejected as closure evidence |

## Result

No non-circular proof of the selector-admissible base-zone coordinate source
premise is available after v2.251. The available Lean bridge is still
conditional on realization/separation data and does not construct it.

The exact immediate no-closure blocker remains:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296
```

## Upstream Chain

The next Lean bridge is:

```lean
physicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296_of_baseZoneOriginCertificateSource1296
```

with direction:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296
  -> PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296
```

The v2.247 recheck records that this realization/separation premise remains
blocked at:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296
```

and v2.248 records the origin-certificate source frontier as blocked at:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296
```

Those facts are upstream context only. This v2.252 recheck does not claim
closure of any upstream premise.

## Downstream Routes Rejected

The following route was not used as proof of the coordinate source premise:

```lean
PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296
  -> PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296
  -> PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296
```

Nor were downstream origin-certificate, residual-value, or separation
interfaces used in reverse to prove the coordinate source premise.

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
CODEX-F3-BASE-ZONE-COORDINATE-REALIZATION-SEPARATION-PREMISE-RECHECK-AFTER-V2-252-001
```

Recheck whether a non-circular source now proves
`PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296`
after v2.252. Do not treat downstream coordinate source, coordinate injection,
tag-coordinate, origin-certificate, residual-value, or separation interfaces as
proof of that premise.
