# F3 Base-Zone Residual Value Code Separation Attempt v2.235

Task: `CODEX-F3-PROVE-BASE-ZONE-RESIDUAL-VALUE-CODE-SEPARATION-001`
Status: `DONE_NO_CLOSURE_SELECTOR_INDEPENDENT_RESIDUAL_VALUE_CODE_MISSING`
Timestamp: `2026-04-28T07:35:00Z`

## Target

Attempted target:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSeparation1296
```

The v2.234 interface and bridge are present:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSeparationData
PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSeparation1296
physicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealization1296_of_baseZoneResidualValueCodeSeparation1296
```

## Result

No Lean proof was added.  The current Lean API does not construct the
selector-independent residual-value code

```lean
∀ residual,
  {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} → Fin 1296
```

on the whole residual subtype with the selected-admissible equality-reflection
law required by
`PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSeparationData`.

The exact no-closure blocker is a non-circular construction of that data from
the v2.121 residual-fiber hypotheses:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSeparationData
```

for every residual-fiber instance, with
`selectorAdmissible_code_injective` proving that equal residual-value codes
force `a.1 = b.1` whenever both residual values carry
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` evidence from
essential parents.

## Why Existing Artifacts Do Not Close It

- The v2.234 Prop/interface cannot be used as evidence for itself.
- `PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealization1296`
  is downstream of v2.234 through the erasure bridge, so using it would be
  circular.
- `PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296` and
  `PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296`
  are farther downstream of the same residual-value code chain and cannot
  supply the separation theorem without reversing the bridge direction.
- Terminal-neighbor selector-code or selected-image interfaces separate a
  selected terminal-neighbor image, not the whole residual subtype.
- Root-shell, local-neighbor, local-displacement, parent-relative
  `terminalNeighborCode`, selected-image cardinality, bounded-menu cardinality,
  empirical search, `finsetCodeOfCardLe`, deleted-X shortcuts, and the v2.161
  selector-image cycle are rejected by the task guardrails and were not used.

## Repair Task

The next precise repair task is to find or formalize a structural residual
base-zone invariant that produces a selector-independent code into `Fin 1296`
on the whole residual subtype, together with selected-admissible
equality-reflection, without passing through any downstream residual-value
source/origin interface.

Suggested task id:

```text
CODEX-F3-SCOPE-STRUCTURAL-RESIDUAL-VALUE-CODE-SEPARATION-SOURCE-001
```

It should determine whether the missing construction can be reduced to a
smaller named structural theorem, or whether the v2.234 separation theorem is
already the minimal honest frontier.

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

All three traces remain exactly no larger than:

```text
[propext, Classical.choice, Quot.sound]
```

F3-COUNT remains `CONDITIONAL_BRIDGE`; no status, percentage, README metric,
planner metric, ledger row, proof closure claim, or Clay-level claim moved.
