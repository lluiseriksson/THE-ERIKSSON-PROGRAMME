# F3 Structural Residual-Value Invariant Inventory

Task: `CODEX-F3-STRUCTURAL-RESIDUAL-VALUE-INVARIANT-INVENTORY-001`
Status: `DONE_INVENTORY_CONDITIONAL_COORDINATE_SOURCE_IDENTIFIED`
Timestamp: `2026-04-28T08:25:00Z`

## Target Payload

The v2.234 carrier

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSeparationData
```

needs:

- a selector-independent residual-value code
  ```lean
  ∀ residual,
    {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} → Fin 1296
  ```
- selected-admissible equality-reflection for residual values carrying
  `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` evidence
  from essential parents.

## Candidate Inventory

| Candidate | Direction relative to v2.234 | Verdict |
| --- | --- | --- |
| `PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296` | Upstream conditional source | Best existing candidate. Its data carrier has `baseZoneTagOfResidualValue`, `baseZoneTagIntoFin1296`, and `selectedAdmissible_injective`, which can be repacked into v2.234 separation data. The premise is still unproved. |
| `PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296` | Upstream to the coordinate candidate | Also has the right code/injectivity shape and already bridges to `BookkeepingBaseZoneTagCoordinate1296`; still unproved, with v2.221 reducing it to `PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296`. |
| `PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296` | Upstream proof-relevant source for the injection candidate | Stronger than needed for v2.234. If proved, existing bridges can reach the coordinate candidate, but the source itself is not proved from the current Lean artifacts. |
| `PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296` | Upstream of the selector-admissible source lane | Over-rich coordinate/certificate source. Useful only through the existing coordinate-source chain; not the narrowest v2.234 blocker. |
| `PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCode1296` | Terminal-neighbor selected-image lane | Supplies an ambient code on the residual subtype, but the separation law is only for the chosen `terminalNeighborOfParent` image. It does not cover arbitrary residual values with existential selector-data evidence, so it cannot construct v2.234. |
| `PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCode1296` | Terminal-neighbor selected-image lane | Same gap as ambient value code: code data exists, but equality-reflection is tied to chosen terminal-neighbor selectors, not the whole selected-admissible residual-value relation. |
| `PhysicalPlaquetteGraphResidualFiberBookkeepingTagMap1296` and descendants | Terminal-neighbor/bookkeeping selected-image lane | Useful for terminal-neighbor ambient code, but not a whole-residual selected-admissible equality-reflection theorem for v2.234. |
| `PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealization1296` | Downstream of v2.234 | Prohibited as reverse evidence; v2.234 bridges into this interface by adding a trivial `Unit` realization layer. |
| `PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296` | Downstream of v2.234 through realization | Prohibited as reverse evidence. |
| `PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296` | Farther downstream of the residual-value code chain | Prohibited as reverse evidence. |
| Root-shell, local-neighbor, local-displacement, parent-relative `terminalNeighborCode`, selected-image cardinality, bounded menu cardinality, empirical search, `finsetCodeOfCardLe`, deleted-X shortcut, v2.161 cycle | Unrelated or explicitly forbidden | Not candidates for this task. |

## Best Conditional Source

The narrowest existing Lean-facing candidate is:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296
```

because its data carrier has exactly the fields needed to define:

```lean
residualValueCode residual q :=
  baseZoneTagIntoFin1296 residual
    (baseZoneTagOfResidualValue residual q)
```

and its `selectedAdmissible_injective` field matches v2.234's
`selectorAdmissible_code_injective` law.

There is no existing bridge in the Lean file from this coordinate theorem into
v2.234.  Adding that bridge would be a no-new-math repackaging step, analogous
to the existing bridge from
`PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296`
to `PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296`.

## Remaining Mathematical Blocker

Even after such a bridge, the substantive blocker remains proving the upstream
coordinate theorem.  Prior artifacts already record:

- v2.219: `PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296`
  does not close; blocker is
  `PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296`.
- v2.221: `PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296`
  does not close; blocker is
  `PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296`.

So the inventory does **not** prove v2.234 and does **not** close F3-COUNT.  It
identifies the best conditional source and the missing formal bridge.

## Next Task

```text
CODEX-F3-BASE-ZONE-TAG-COORDINATE-TO-RESIDUAL-VALUE-SEPARATION-BRIDGE-001
```

Prove, without `sorry` or new axioms:

```lean
physicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSeparation1296_of_residualFiberBookkeepingBaseZoneTagCoordinate1296
```

with premise:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296
```

and target:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSeparation1296
```

The bridge should only repack `baseZoneTagOfResidualValue`,
`baseZoneTagIntoFin1296`, and `selectedAdmissible_injective` into
`PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSeparationData`.

## Validation

Dashboard-only inventory. No Lean file was edited, so no `lake build` was
required.

YAML/JSON/JSONL validation passed after registry updates.

F3-COUNT remains `CONDITIONAL_BRIDGE`; no status, percentage, README metric,
planner metric, ledger row, proof closure claim, or Clay-level claim moved.
