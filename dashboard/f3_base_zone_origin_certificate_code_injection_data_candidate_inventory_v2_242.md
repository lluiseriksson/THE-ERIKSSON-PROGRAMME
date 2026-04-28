# F3 v2.242: Direct Data Candidates for Origin Certificate Code Injection

Task: `CODEX-F3-BASE-ZONE-ORIGIN-CERTIFICATE-CODE-INJECTION-DATA-CANDIDATE-INVENTORY-001`

Status: `DONE_INVENTORY_NO_UNCONDITIONAL_SOURCE_DIRECT_CONDITIONAL_BRIDGE_IDENTIFIED`

## Objective

Inventory concrete v2.121 bookkeeping/base-zone invariants that could construct
`PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjectionData`
directly. The required data carrier is:

- a selector-independent whole-residual code
  `baseZoneOriginCertificateCode : ∀ residual, {q // q ∈ residual} -> Fin 1296`;
- selected-admissible equality-reflection for any two residual values carrying
  terminal-neighbor selector-data evidence from some essential parent.

This inventory does not use `PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296`
or downstream residual-value realization/separation interfaces as proof evidence.

## Candidate Inventory

| Candidate invariant/interface | Bridge direction relative to code injection | Result |
| --- | --- | --- |
| v2.121 base-aware bookkeeping data from `physicalPlaquetteGraph_baseAwareTerminalPredecessorBookkeeping1296` (`deleted`, `parentOf`, `essential`) | Upstream hypotheses | Supplies residual deletion/parent/essential bookkeeping and `essential residual ⊆ residual`, but no whole-residual `Fin 1296` code and no selected-admissible equality-reflection. Not enough. |
| `PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinateData` / `PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296` | Upstream conditional direct source | This is the narrowest existing named carrier with the exact shape needed after erasure: compose `baseZoneTagOfResidualValue` with `baseZoneTagIntoFin1296`, and reuse `selectedAdmissible_injective`. The theorem premise is still unproved, so it does not close code injection from v2.121. |
| `PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjectionData` / `...CoordinateInjection1296` | Upstream conditional direct source | Also has the required whole-residual coordinate into `Fin 1296` plus selected-admissible equality-reflection. It is at least as strong as the tag-coordinate carrier and remains unproved. |
| `PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSourceData` / `...CoordinateSource1296` | Upstream stronger source | Can erase realization witnesses to a code-injection datum, but it is stronger than the direct injection carrier and remains unproved. |
| `PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparationData` / `...RealizationSeparation1296` | Upstream stronger realization source | Can erase origin/realization structure to a code-injection datum, but it is not the narrowest blocker and remains unproved. |
| `PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSourceData` / `...OriginCertificateSource1296` | Richer source, not the narrowest source for this frontier | The data can be erased to code-injection data, but the supported v2.228 bridge direction is from code injection to origin-certificate source. Treating this downstream/richer interface as evidence would not identify a smaller non-circular source. |
| `PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSeparationData`, `...ResidualValueCodeSourceData`, and residual-value realization/source/separation interfaces | Downstream/prohibited | Explicitly excluded by the task. They are not proof evidence for this inventory. |
| Terminal-neighbor ambient or bookkeeping tag code lanes | Unrelated/insufficient | Existing code interfaces are fixed-selector or selected-image oriented. They do not provide the required existential selected-admissible equality-reflection over the whole residual subtype. |

Forbidden routes were not used: selected-image cardinality, bounded menu cardinality,
empirical search, `finsetCodeOfCardLe`, root-shell/local-neighbor/local-displacement
codes, parent-relative `terminalNeighborCode` equality, deleted-X shortcut, and the
v2.161 cycle.

## Narrowest Missing Shape

No existing v2.121 bookkeeping/base-zone invariant proves the code-injection data
unconditionally. The narrowest honest missing invariant is still:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296
```

Equivalently, one may state the missing data shape directly as:

```lean
Nonempty
  (PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinateData
    (L := L) essential)
```

under the same v2.121 residual bookkeeping hypotheses.

Once that coordinate premise is available, the direct bridge to
`PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjectionData`
is a pure repacking:

```lean
baseZoneOriginCertificateCode residual q :=
  tagData.baseZoneTagIntoFin1296 residual
    (tagData.baseZoneTagOfResidualValue residual q)
```

and the required equality-reflection is exactly `tagData.selectedAdmissible_injective`.

## Validation

- Dashboard artifact lists each candidate invariant checked and its bridge direction.
- No proposed theorem routes through residual-value code source, realization, or separation.
- No Lean theorem was added; no `lake build` was required.
- `F3-COUNT` remains `CONDITIONAL_BRIDGE`; no percentage, README metric, planner
  metric, ledger row, proof closure claim, or Clay-level claim moved.

