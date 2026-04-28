# F3 base-zone origin certificate code-injection frontier recheck v2.240

Task: `CODEX-F3-BASE-ZONE-ORIGIN-CERTIFICATE-CODE-INJECTION-FRONTIER-RECHECK-001`

Status: `DONE_NO_CLOSURE_NONCIRCULAR_CODE_INJECTION_DATA_MISSING`

Timestamp: `2026-04-28T09:55:00Z`

## Rechecked Target

Current code-injection frontier:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296
```

The v2.228 interface and bridge are present:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjectionData
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296
physicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296_of_baseZoneOriginCertificateCodeInjection1296
```

The bridge direction is:

```text
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296
  -> PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296
```

## Lean Source Check

The current Lean file contains one named theorem that produces the target from
another F3 interface:

```lean
physicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296_of_baseZoneResidualValueCodeSource1296
```

with bridge direction:

```text
PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296
  -> PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296
```

That theorem is a valid no-sorry repackaging bridge, but it is not an admissible
closure route for this task.  In the post-v2.236 chain,
`PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296` is
downstream of residual-value realization/separation, and using it here would
route through the circular lane already isolated in v2.239.

## No-Closure Result

No non-circular structural source was found for:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296
```

under the task guardrails.

The exact no-closure blocker is the missing direct construction of:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjectionData
```

from v2.121 bookkeeping/base-zone residual data, specifically:

- `baseZoneOriginCertificateCode` on the whole residual subtype
  `{q // q ∈ residual} -> Fin 1296`;
- `selectorAdmissible_code_injective`, reflecting equality of codes back to
  equality of residual values when both values carry
  `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` evidence
  from essential parents.

Equivalently, the missing theorem is a new upstream structural source for the
code-injection data that is not `PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296`
and does not factor through residual-value realization, residual-value
separation, selected-image cardinality, bounded menus, empirical search, local
codes, or the v2.161 cycle.

## Rejected Routes

This recheck did not use downstream residual-value source/realization/separation
interfaces in reverse or as circular evidence.  It also did not use
selected-image cardinality, bounded menu cardinality, empirical search,
`finsetCodeOfCardLe`, root-shell codes, local-neighbor codes,
local-displacement codes, parent-relative `terminalNeighborCode` equality,
deleted-X shortcuts, or the v2.161 cycle.

## Validation

No Lean file was edited, so no `lake build` was required by this task.  No new
theorem was added and no new theorem-specific axiom trace was introduced.

F3-COUNT remains `CONDITIONAL_BRIDGE`.  No status, percentage, README metric,
planner metric, ledger row, proof closure claim, or Clay-level claim moved.

## Next Task

```text
CODEX-F3-BASE-ZONE-ORIGIN-CERTIFICATE-CODE-INJECTION-STRUCTURAL-SOURCE-SCOPE-001
```

Scope a new non-circular structural source for
`PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296`
or confirm that the v2.228 data carrier itself is the minimal honest frontier.
The task must not use `PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296`
or downstream residual-value realization/separation interfaces as proof
evidence.
