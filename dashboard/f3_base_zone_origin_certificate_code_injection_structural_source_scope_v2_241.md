# F3 base-zone origin certificate code-injection structural source scope v2.241

Task: `CODEX-F3-BASE-ZONE-ORIGIN-CERTIFICATE-CODE-INJECTION-STRUCTURAL-SOURCE-SCOPE-001`

Status: `DONE_SCOPE_MINIMAL_FRONTIER_CONFIRMED`

Timestamp: `2026-04-28T10:15:00Z`

## Scoped Target

The current frontier is:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296
```

with data carrier:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjectionData
```

The downstream bridge already landed in v2.228:

```lean
physicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296_of_baseZoneOriginCertificateCodeInjection1296
```

Bridge direction:

```text
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296
  -> PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296
```

## Minimal Frontier Decision

No strictly upstream named theorem was found that is both:

1. narrower than `PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjectionData`; and
2. independent of downstream residual-value source/realization/separation
   interfaces.

The honest minimal frontier is therefore the direct construction of:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjectionData
```

from the v2.121 bookkeeping/base-zone residual configuration.

Introducing a new theorem merely named
`...StructuralSource1296` would not reduce the mathematical payload unless it
constructs the same two fields from additional, concrete upstream structure:

- `baseZoneOriginCertificateCode` on the whole residual subtype
  `{q // q ∈ residual} -> Fin 1296`;
- `selectorAdmissible_code_injective`, reflecting equal codes to equal
  residual values for values carrying
  `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` evidence
  from essential parents.

## Candidate Review

| Candidate | Direction | Scope verdict |
| --- | --- | --- |
| `PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjectionData` | Exact carrier for the target | Minimal honest frontier. It contains exactly the residual-wide `Fin 1296` code and selected-admissible equality-reflection law. |
| `PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296` | Upstream of v2.234 residual-value separation | Not a non-circular source for code injection here. Using it reaches code injection only through the v2.236 residual-value separation and downstream realization/source chain. |
| `PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296` | Upstream of bookkeeping base-zone tag coordinate | Same problem: it can feed the coordinate/residual-value separation lane, but code injection would be reached only through downstream residual-value interfaces. |
| `PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296` | Upstream of selector-admissible coordinate source | Not a direct code-injection source; its bridge direction feeds the coordinate chain and then the residual-value lane. |
| `PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296` | Downstream of residual-value realization/separation | Explicitly disallowed as proof evidence for this scope. |
| Terminal-neighbor selected-image/ambient/bookkeeping code lanes | Selected-image or terminal-neighbor-local direction | Not sufficient for a whole-residual code-injection theorem with existential selected-admissible equality-reflection. |
| Root-shell, local-neighbor, local-displacement, parent-relative `terminalNeighborCode`, selected-image cardinality, bounded menus, empirical search, `finsetCodeOfCardLe`, deleted-X shortcut, v2.161 cycle | Unrelated or forbidden | Rejected by the task guardrails. |

## Exact Blocker

The next no-closure blocker is:

```text
Construct PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjectionData
directly from v2.121 bookkeeping/base-zone residual data.
```

This is not closed by the current Lean artifacts.  It requires a structural
residual/base-zone invariant that supplies a selector-independent `Fin 1296`
code on the whole residual subtype and proves selected-admissible
equality-reflection using essential-parent terminal-neighbor selector evidence.

## Rejected Routes

This scope did not use `PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296`
or downstream residual-value realization/separation interfaces as evidence. It
also did not use selected-image cardinality, bounded menu cardinality,
empirical search, `finsetCodeOfCardLe`, root-shell codes, local-neighbor codes,
local-displacement codes, parent-relative `terminalNeighborCode` equality,
deleted-X shortcuts, or the v2.161 cycle.

## Validation

This was a dashboard-only scope.  No Lean theorem was added and no Lean file was
edited, so no `lake build` or new theorem-specific axiom trace was required.

F3-COUNT remains `CONDITIONAL_BRIDGE`.  No status, percentage, README metric,
planner metric, ledger row, proof closure claim, or Clay-level claim moved.

## Next Task

```text
CODEX-F3-BASE-ZONE-ORIGIN-CERTIFICATE-CODE-INJECTION-DATA-CANDIDATE-INVENTORY-001
```

Inventory concrete v2.121 bookkeeping/base-zone invariants that could construct
`PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjectionData`
directly.  The inventory must not route through downstream residual-value
source/realization/separation interfaces.
