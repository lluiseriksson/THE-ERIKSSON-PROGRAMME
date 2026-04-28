# F3 v2.249: Origin Certificate Code Injection Via Tag Coordinate Recheck

Task: `CODEX-F3-BASE-ZONE-ORIGIN-CERTIFICATE-CODE-INJECTION-VIA-TAG-COORDINATE-RECHECK-AFTER-V2-248-001`

Status: `DONE_NO_CLOSURE_BOOKKEEPING_BASE_ZONE_TAG_COORDINATE_STILL_MISSING`

Timestamp: `2026-04-28T16:15:22Z`

## Checked Target

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296
```

The post-v2.243 Lean bridge into this target is:

```lean
physicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296_of_residualFiberBookkeepingBaseZoneTagCoordinate1296
```

Bridge direction:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296
  -> PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296
```

## Result

The tag-coordinate route does not prove the code-injection target
unconditionally. It is a valid no-sorry conditional bridge, but its premise is
still open:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296
```

The exact remaining no-closure blocker for this recheck is therefore:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296
```

The bridge repacks:

```lean
baseZoneOriginCertificateCode residual q :=
  coordinateData.baseZoneTagIntoFin1296 residual
    (coordinateData.baseZoneTagOfResidualValue residual q)
```

and reuses:

```lean
coordinateData.selectedAdmissible_injective
```

This removes only the formal repackaging gap from a tag-coordinate carrier to
origin-certificate code injection. It does not construct the tag-coordinate
carrier from v2.121 bookkeeping data.

## Upstream Chain Reminder

The Lean file also has:

```lean
physicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296_of_residualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296
```

with direction:

```lean
PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296
  -> PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296
```

Prior artifacts record that this upstream premise remains unproved. It is not
used here as closure of the tag-coordinate premise.

## Rejected Routes

This recheck does not use:

- downstream residual-value source, realization, origin, or separation
  interfaces in reverse;
- selected-image cardinality;
- bounded menu cardinality;
- empirical search;
- `finsetCodeOfCardLe`;
- root-shell/local-neighbor/local-displacement codes;
- parent-relative `terminalNeighborCode` equality;
- deleted-X shortcuts;
- the v2.161 cycle.

## Validation

No Lean file was edited, so no `lake build` was required. No new theorem or
theorem-specific axiom trace was introduced.

F3-COUNT remains `CONDITIONAL_BRIDGE`. No status, percentage, README metric,
planner metric, ledger row, proof closure claim, or Clay-level claim moved.

## Next Task

```text
CODEX-F3-BOOKKEEPING-BASE-ZONE-TAG-COORDINATE-PREMISE-RECHECK-AFTER-V2-249-001
```

Recheck whether a non-circular source now proves
`PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296` after
the v2.249 conditional code-injection recheck. Do not treat downstream
origin-certificate, residual-value, or code-injection interfaces as proof of
this premise.
