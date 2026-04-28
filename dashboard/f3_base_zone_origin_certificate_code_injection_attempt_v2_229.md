# F3 Base-Zone Origin Certificate Code Injection Attempt v2.229

Task: `CODEX-F3-PROVE-BASE-ZONE-ORIGIN-CERTIFICATE-CODE-INJECTION-001`
Status: `DONE_NO_CLOSURE_RESIDUAL_VALUE_CODE_SOURCE_MISSING`
Timestamp: `2026-04-28T04:25:00Z`

## Target

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296
```

The v2.228 Lean interface and bridge are present:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjectionData
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296
physicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296_of_baseZoneOriginCertificateCodeInjection1296
```

## Result

This proof attempt does not close the target. The current Lean API exposes the
v2.228 code-injection interface and the erasure bridge into
`PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296`, but it
does not yet construct the needed selector-independent residual-value code into
`Fin 1296` on the whole residual subtype.

The exact missing source is a theorem of the following shape:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296
```

It should supply, for each v2.121 bookkeeping residual fiber:

- a selector-independent code `{q // q ∈ residual} -> Fin 1296`;
- a structural residual/base-zone origin for that code, independent of a fixed
  selected image or bounded menu;
- selected-admissible equality-reflection for residual values carrying
  `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` evidence
  from essential parents.

The expected downstream bridge is:

```lean
physicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296_of_baseZoneResidualValueCodeSource1296
```

That bridge would package the residual-value code and equality-reflection into
`PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjectionData`.

## Rejected Routes

This attempt explicitly does not use selected-image cardinality, bounded menu
cardinality, empirical search, `finsetCodeOfCardLe`, root-shell codes,
local-neighbor codes, local-displacement codes, parent-relative
`terminalNeighborCode` equality, the deleted-X shortcut, or the v2.161 circular
selector-image chain.

The visible Lean candidates in this region are the v2.228 interface/bridge and
older coding lemmas in those rejected families. They are not enough to produce
the residual-wide selector-independent code required here.

## Validation

- `lake build YangMills.ClayCore.LatticeAnimalCount` passed.
- No new Lean theorem was added in this proof attempt, so there is no new
  theorem-specific axiom trace.
- The existing v2.228 interface/bridge traces remain no larger than
  `[propext, Classical.choice, Quot.sound]`.
- F3-COUNT remains `CONDITIONAL_BRIDGE`; no status, percentage, README metric,
  planner metric, ledger row, proof closure claim, or Clay-level claim moved.

## Next Task

```text
CODEX-F3-BASE-ZONE-RESIDUAL-VALUE-CODE-SOURCE-SCOPE-001
```
