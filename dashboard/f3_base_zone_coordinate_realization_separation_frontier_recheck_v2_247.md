# F3 v2.247: Base-Zone Coordinate Realization/Separation Frontier Recheck

Task: `CODEX-F3-BASE-ZONE-COORDINATE-REALIZATION-SEPARATION-FRONTIER-RECHECK-001`

Status: `DONE_NO_CLOSURE_ORIGIN_CERTIFICATE_SOURCE_STILL_MISSING`

Timestamp: `2026-04-28T16:06:31Z`

## Checked Target

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296
```

The Lean bridge into this target is still:

```lean
physicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296_of_baseZoneOriginCertificateSource1296
```

Bridge direction:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296
  -> PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296
```

## Result

No non-circular proof of the realization/separation target is available after
v2.246. The v2.224/v2.226 interface stack gives a conditional bridge, but it
does not construct the required selector-independent origin certificate source.

The exact remaining immediate blocker is:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296
```

## Current Upstream Shape

The post-v2.226 Lean file also contains:

```lean
physicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296_of_baseZoneOriginCertificateCodeInjection1296
```

with direction:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296
  -> PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296
```

That bridge is upstream of the source frontier, but it is still conditional. It
does not prove `PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296`
unless a non-circular code-injection source is supplied.

The later tag-coordinate bridge:

```lean
physicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296_of_residualFiberBookkeepingBaseZoneTagCoordinate1296
```

also remains conditional on:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296
```

which prior artifacts have not closed. This recheck therefore records the
realization/separation frontier blocker exactly at the source premise, not as a
proof of the target.

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
CODEX-F3-BASE-ZONE-ORIGIN-CERTIFICATE-SOURCE-FRONTIER-RECHECK-AFTER-V2-247-001
```

Recheck whether a non-circular source now proves
`PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296` after
the v2.247 realization/separation recheck and the post-v2.243 conditional
bridges, or preserve the immediate upstream blocker without using downstream
residual-value interfaces in reverse.
