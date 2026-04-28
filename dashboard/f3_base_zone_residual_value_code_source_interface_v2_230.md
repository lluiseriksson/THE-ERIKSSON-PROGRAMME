# F3 Base-Zone Residual Value Code Source Interface v2.230

Task: `CODEX-F3-BASE-ZONE-RESIDUAL-VALUE-CODE-SOURCE-INTERFACE-001`
Status: `DONE_INTERFACE_AND_BRIDGE_LANDED`
Timestamp: `2026-04-28T04:50:00Z`

## Lean Additions

- Added `PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSourceData`.
- Added `PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296`.
- Added `physicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296_of_baseZoneResidualValueCodeSource1296`.

The new interface is strictly upstream of `PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296`.

It exposes a proof-relevant residual-value code source layer on the whole residual subtype:

- `residualValueCodeSource`
- `residualValueCodeSourceOfValue`
- `residualValueSource_valid`
- `residualValueCodeSourceOfValue_valid`
- `residualValueCodeOfSource : ... -> Fin 1296`
- `residualValueCode_source_ext`
- `selectorAdmissible_sourceCode_injective`

The selected-admissible equality-reflection statement is restricted to residual values carrying `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` evidence from essential parents.

## Bridge

Bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296
```

Bridge theorem:

```lean
physicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296_of_baseZoneResidualValueCodeSource1296
```

The bridge forgets the proof-relevant source layer by defining the v2.228 code as:

```lean
fun residual q =>
  residualValueCodeOfSource residual q
    (residualValueCodeSourceOfValue residual q)
```

and uses `selectorAdmissible_sourceCode_injective` to prove `selectorAdmissible_code_injective`.
This is erasure/projection only. It does not prove the source theorem and does not close F3-COUNT.

## Guardrails

This interface rejects selected-image cardinality, bounded menu cardinality, empirical search, `finsetCodeOfCardLe`, root-shell codes, local-neighbor codes, local-displacement codes, parent-relative `terminalNeighborCode` equality, deleted-X shortcuts, and the v2.161 cycle.

## Validation

- `lake build YangMills.ClayCore.LatticeAnimalCount` passed.
- New `#print axioms` traces for the data, Prop/interface, and bridge are no larger than `[propext, Classical.choice, Quot.sound]`.
- F3-COUNT remains `CONDITIONAL_BRIDGE`; no status, percentage, README metric, planner metric, ledger row, proof closure claim, or Clay-level claim moved.

## Next Blocker

Prove:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296
```

or reduce it to the next exact no-closure blocker.
