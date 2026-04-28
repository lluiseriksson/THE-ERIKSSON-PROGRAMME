# F3 v2.254: Base-Zone Origin Certificate Source Premise Recheck

Task: `CODEX-F3-BASE-ZONE-ORIGIN-CERTIFICATE-SOURCE-PREMISE-RECHECK-AFTER-V2-253-001`

Status: `DONE_NO_CLOSURE_BASE_ZONE_ORIGIN_CERTIFICATE_CODE_INJECTION_STILL_MISSING`

Timestamp: `2026-04-28T16:38:17Z`

## Checked Target

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296
```

The direct Lean bridge into this target remains:

```lean
physicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296_of_baseZoneOriginCertificateCodeInjection1296
```

Bridge direction:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296
  -> PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296
```

## Candidate Sources Checked

| Candidate | Direction | Result |
| --- | --- | --- |
| `PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296` | Upstream into origin-certificate source | Valid conditional bridge, but premise still open |
| `PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296` | Conditional route into code injection | Rejected as closure evidence because the tag-coordinate premise remains open |
| `PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296` | Conditional route into code injection | Rejected as reverse/downstream residual-value evidence in the current chain |
| `PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296` | Downstream from origin-certificate source | Rejected as reverse evidence |
| Coordinate source, coordinate injection, residual-value realization/origin/separation interfaces | Downstream/conditional in the current chain | Rejected as reverse evidence |

## Result

No non-circular proof of the base-zone origin certificate source premise is
available after v2.253. The available Lean bridge is still conditional on a
selector-independent origin-certificate code injection and does not construct
that code injection.

The exact immediate no-closure blocker remains:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296
```

## Upstream Chain

The post-v2.243 Lean bridge is:

```lean
physicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296_of_residualFiberBookkeepingBaseZoneTagCoordinate1296
```

with direction:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296
  -> PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296
```

The v2.249 recheck records that this route remains blocked at:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296
```

The v2.250 recheck records the tag-coordinate premise as blocked at:

```lean
PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296
```

Those facts are upstream context only. This v2.254 recheck does not claim
closure of any upstream premise.

## Rejected Residual-Value Route

The Lean file also contains:

```lean
physicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296_of_baseZoneResidualValueCodeSource1296
```

with direction:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296
  -> PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296
```

This route was not used. In the current chain, residual-value source is not a
non-circular source for the origin-certificate source premise, and using it as
closure would violate the downstream residual-value guardrail.

## Downstream Routes Rejected

The following route was not used as proof of the origin-certificate source
premise:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296
  -> PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296
  -> PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296
  -> PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296
```

Nor were downstream coordinate injection, bookkeeping tag-coordinate,
origin-certificate, residual-value, or separation interfaces used in reverse.

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
CODEX-F3-BASE-ZONE-ORIGIN-CERTIFICATE-CODE-INJECTION-PREMISE-RECHECK-AFTER-V2-254-001
```

Recheck whether a non-circular source now proves
`PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296`
after v2.254. Do not treat downstream origin-certificate source,
realization/separation, coordinate source, coordinate injection,
tag-coordinate, residual-value, or separation interfaces as proof of that
premise.
