# F3 Base-Zone Residual Value Code Realization Interface v2.232

Task: `CODEX-F3-BASE-ZONE-RESIDUAL-VALUE-CODE-REALIZATION-INTERFACE-001`
Status: `DONE_INTERFACE_AND_BRIDGE_LANDED`
Timestamp: `2026-04-28T05:55:00Z`

## Lean Additions

- Added `PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealizationData`.
- Added `PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealization1296`.
- Added `physicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296_of_baseZoneResidualValueCodeRealization1296`.

The new interface is strictly upstream of
`PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296`.

It exposes proof-relevant residual-value code realization data on the whole
residual subtype:

- `residualValueCodeRealization`
- `residualValueCodeRealizationOfValue`
- `residualValueCodeRealization_valid`
- `residualValueCodeRealizationOfValue_valid`
- `residualValueCodeOfRealization : ... -> Fin 1296`
- `residualValueCode_realization_ext`
- `selectorAdmissible_realizedCode_injective`

The selected-admissible equality-reflection statement is restricted to
residual values carrying
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` evidence from
essential parents.

## Bridge

Bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296
```

Bridge theorem:

```lean
physicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296_of_baseZoneResidualValueCodeRealization1296
```

The bridge erases the realization/certificate layer by projecting realization
fields directly into the v2.230 source fields:

```lean
residualValueCodeSource := residualValueCodeRealization
residualValueCodeSourceOfValue := residualValueCodeRealizationOfValue
residualValueSource_valid := residualValueCodeRealization_valid
residualValueCodeSourceOfValue_valid :=
  residualValueCodeRealizationOfValue_valid
residualValueCodeOfSource := residualValueCodeOfRealization
residualValueCode_source_ext := residualValueCode_realization_ext
selectorAdmissible_sourceCode_injective :=
  selectorAdmissible_realizedCode_injective
```

This is structural erasure/projection only.  It does not prove the realization
theorem and does not close F3-COUNT.

## Guardrails

This interface rejects selected-image cardinality, bounded menu cardinality,
empirical search, `finsetCodeOfCardLe`, root-shell codes, local-neighbor codes,
local-displacement codes, parent-relative `terminalNeighborCode` equality,
deleted-X shortcuts, and the v2.161 cycle.

It does not merely restate
`PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296`:
the new carrier isolates a realization/certificate layer that is erased into
the source interface by the bridge.

## Validation

- `lake build YangMills.ClayCore.LatticeAnimalCount` passed.
- New `#print axioms` traces for the data, Prop/interface, and bridge are no
  larger than `[propext, Classical.choice, Quot.sound]`.
- F3-COUNT remains `CONDITIONAL_BRIDGE`; no status, percentage, README metric,
  planner metric, ledger row, proof closure claim, or Clay-level claim moved.

## Next Blocker

Prove:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealization1296
```

or reduce it to the next exact no-closure blocker.
