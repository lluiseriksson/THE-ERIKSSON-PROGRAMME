# F3 Base-Zone Residual Value Code Separation Interface v2.234

Task: `CODEX-F3-BASE-ZONE-RESIDUAL-VALUE-CODE-SEPARATION-INTERFACE-001`
Status: `DONE_INTERFACE_AND_BRIDGE_LANDED`
Timestamp: `2026-04-28T06:55:00Z`

## Lean Additions

Added the focused no-sorry residual-value code separation carrier:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSeparationData
```

Added the Prop/interface:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSeparation1296
```

Added the erasure bridge:

```lean
physicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealization1296_of_baseZoneResidualValueCodeSeparation1296
```

The bridge target is exactly:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealization1296
```

## Interface Shape

The data carrier exposes only:

- `residualValueCode`, a selector-independent code into `Fin 1296` on the
  whole residual subtype;
- `selectorAdmissible_code_injective`, an equality-reflection law restricted to
  residual values carrying
  `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` evidence
  from essential parents.

It does not carry a selected image, bounded menu, empirical witness, root-shell
code, local-neighbor code, local-displacement code, or parent-relative
`terminalNeighborCode`.

## Bridge

The bridge into v2.232 is structural repackaging only:

```lean
residualValueCodeRealization := fun _ _ => Unit
residualValueCodeRealizationOfValue := fun _ _ => ()
residualValueCodeRealization_valid := fun _ _ _ => True
residualValueCodeRealizationOfValue_valid := fun _ _ => trivial
residualValueCodeOfRealization := fun residual q _ =>
  separationData.residualValueCode residual q
residualValueCode_realization_ext := by intros; rfl
selectorAdmissible_realizedCode_injective :=
  separationData.selectorAdmissible_code_injective
```

The mathematical content remains in the separation interface; the bridge only
adds the trivial `Unit` realization layer.

## Guardrails

This interface rejects selected-image cardinality, bounded menu cardinality,
empirical search, `finsetCodeOfCardLe`, root-shell codes, local-neighbor codes,
local-displacement codes, parent-relative `terminalNeighborCode` equality,
deleted-X shortcuts, and the v2.161 selector-image cycle.

It does not merely restate
`PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealization1296`:
the new carrier removes the realization/certificate layer and isolates the
residual-value code plus selected-admissible equality-reflection.

## Validation

Command:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result: passed.

Focused axiom check:

```text
PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSeparationData
PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSeparation1296
physicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealization1296_of_baseZoneResidualValueCodeSeparation1296
```

All three traces are no larger than:

```text
[propext, Classical.choice, Quot.sound]
```

F3-COUNT remains `CONDITIONAL_BRIDGE`; no status, percentage, README metric,
planner metric, ledger row, proof closure claim, or Clay-level claim moved.

## Next Task

```text
CODEX-F3-PROVE-BASE-ZONE-RESIDUAL-VALUE-CODE-SEPARATION-001
```

Prove `PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSeparation1296`
or reduce it to the next exact no-closure blocker.
