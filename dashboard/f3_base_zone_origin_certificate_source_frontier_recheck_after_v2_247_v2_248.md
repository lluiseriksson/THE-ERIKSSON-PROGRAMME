# F3 v2.248: Base-Zone Origin Certificate Source Frontier Recheck After v2.247

Task: `CODEX-F3-BASE-ZONE-ORIGIN-CERTIFICATE-SOURCE-FRONTIER-RECHECK-AFTER-V2-247-001`

Status: `DONE_NO_CLOSURE_ORIGIN_CERTIFICATE_CODE_INJECTION_STILL_MISSING`

Timestamp: `2026-04-28T16:11:04Z`

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

## Result

No non-circular proof of the origin-certificate source target is available after
v2.247 and the post-v2.243 conditional bridge work. The v2.228/v2.226 bridge
stack repacks code-injection data into origin-certificate source data, but it
does not construct the required selector-independent code injection.

The exact immediate blocker remains:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296
```

## Post-v2.243 Conditional Route

The Lean file contains the post-v2.243 bridge:

```lean
physicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296_of_residualFiberBookkeepingBaseZoneTagCoordinate1296
```

with direction:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296
  -> PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296
```

Composing this bridge with the source bridge would give a conditional route:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296
  -> PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296
  -> PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296
```

This is not a closure because
`PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296`
remains open. Prior artifacts reduce that premise through the
selector-admissible base-zone coordinate chain and do not provide a new
non-circular proof at this frontier.

## Rejected Route

The Lean file also contains:

```lean
physicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296_of_baseZoneResidualValueCodeSource1296
```

This bridge has direction:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296
  -> PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296
```

It was not used. In the current chain, residual-value source is downstream of
residual-value realization/separation and would be circular proof evidence for
this source frontier.

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
CODEX-F3-BASE-ZONE-ORIGIN-CERTIFICATE-CODE-INJECTION-VIA-TAG-COORDINATE-RECHECK-AFTER-V2-248-001
```

Recheck whether the post-v2.243 tag-coordinate route can prove
`PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296`
without treating the still-open tag-coordinate premise as closure; otherwise
record the exact blocker at
`PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296`.
