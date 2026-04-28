# F3 Base-Zone Residual Value Code Realization Attempt v2.233

Task: `CODEX-F3-PROVE-BASE-ZONE-RESIDUAL-VALUE-CODE-REALIZATION-001`
Status: `DONE_NO_CLOSURE_RESIDUAL_VALUE_CODE_SEPARATION_MISSING`
Timestamp: `2026-04-28T06:10:00Z`

## Target

Attempted target:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealization1296
```

The v2.232 interface and bridge are present:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealizationData
PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealization1296
physicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296_of_baseZoneResidualValueCodeRealization1296
```

## Result

No Lean proof was added.  The current Lean API does not construct the actual
selector-independent residual-value code and selected-admissible
equality-reflection needed to populate
`PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealizationData`.

The v2.232 carrier still requires the following proof content:

```lean
residualValueCodeRealization
residualValueCodeRealizationOfValue
residualValueCodeRealization_valid
residualValueCodeRealizationOfValue_valid
residualValueCodeOfRealization
residualValueCode_realization_ext
selectorAdmissible_realizedCode_injective
```

A trivial realization carrier such as `Unit` would make realization validity
and realization-choice stability easy, but it would still require a genuine
selector-independent residual-value code

```lean
{q : ConcretePlaquette physicalClayDimension L // q ∈ residual} -> Fin 1296
```

whose equality reflects equality of selector-admissible residual values carrying
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` evidence from
essential parents.  That code/separation principle is not available in the
current Lean artifacts.

Using the v2.232 interface itself as evidence would be circular and was not
done.

## Existing Candidates Are Insufficient

- `PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296` is
  downstream of v2.232 through
  `physicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296_of_baseZoneResidualValueCodeRealization1296`,
  so using it would reverse the intended bridge chain.
- `PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296`
  is farther downstream of the same chain and cannot supply the realization
  theorem without circularity.
- root-shell codes only code first-shell/root-neighbor objects, not arbitrary
  values in the residual subtype.
- local-neighbor and local-displacement codes are edge-local or parent-local
  and do not provide residual-subtype bookkeeping/base-zone equality-reflection.
- `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData.terminalNeighborCode`
  is parent-relative selector data, not a selector-independent residual-value
  code.
- selected-image cardinality, bounded menu cardinality, empirical search, and
  `finsetCodeOfCardLe` would violate the lane guardrails.

## Exact No-Closure Blocker

The next missing structural theorem should isolate the residual-value code and
its selected-admissible equality-reflection, tentatively:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSeparation1296
```

Expected bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealization1296
```

Expected bridge idea:

1. assume a selector-independent residual-value code into `Fin 1296` on the
   whole residual subtype;
2. assume selected-admissible equality-reflection for values carrying
   terminal-neighbor selector data from essential parents;
3. instantiate `residualValueCodeRealization` as `Unit`;
4. mark the unique realization valid;
5. define `residualValueCodeOfRealization residual q ()` by the supplied code;
6. discharge realization-choice stability by cases on `Unit`;
7. discharge `selectorAdmissible_realizedCode_injective` with the supplied
   separation theorem.

The bridge into v2.232 should be erasure/repackaging only.  The mathematical
content remains in the residual-value code separation theorem.

## Rejected Routes

This attempt did not use selected-image cardinality, bounded menu cardinality,
empirical search, `finsetCodeOfCardLe`, root-shell codes, local-neighbor codes,
local-displacement codes, parent-relative `terminalNeighborCode` equality,
deleted-X shortcuts, or the v2.161 selector-image cycle.

## Validation

Command:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result: passed after the v2.232 Lean additions and before this no-closure note;
no further Lean file edits were made in this proof attempt.

The new v2.232 `#print axioms` traces remain no larger than
`[propext, Classical.choice, Quot.sound]`.

F3-COUNT remains `CONDITIONAL_BRIDGE`; no status, percentage, README metric,
planner metric, ledger row, proof closure claim, or Clay-level claim moved.

## Next Task

```text
CODEX-F3-BASE-ZONE-RESIDUAL-VALUE-CODE-SEPARATION-SCOPE-001
```

Scope the structural residual-value code separation theorem and its bridge into
`PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealization1296`.
