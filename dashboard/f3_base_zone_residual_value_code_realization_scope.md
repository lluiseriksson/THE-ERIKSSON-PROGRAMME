# F3 Base-Zone Residual Value Code Realization Scope

Task: `CODEX-F3-BASE-ZONE-RESIDUAL-VALUE-CODE-REALIZATION-SCOPE-001`
Status: `DONE_SCOPE_DELIVERED_NO_LEAN_NO_STATUS_MOVE`
Timestamp: `2026-04-28T05:35:00Z`

## Proposed Upstream Theorem

Tentative Lean target:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealization1296
```

Bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296
```

Expected bridge name:

```lean
physicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296_of_baseZoneResidualValueCodeRealization1296
```

## Purpose

The v2.230 source interface already exposes a proof-relevant source type for
each value of the whole residual subtype:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSourceData
```

The v2.231 proof attempt showed that this is still not concrete enough for
closure.  The missing ingredient is not another copy of that source interface,
but a realization principle explaining where the valid residual-value code
source comes from and why its extracted `Fin 1296` code separates
selector-admissible residual values.

This scope therefore inserts a strictly upstream realization layer.  It should
construct or assume residual-value code realization/certificate data before the
v2.230 `residualValueCodeSource` fields are packaged.

## Why This Is Not A Restatement

The realization theorem must not merely return
`PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSourceData`.
It must isolate a concrete source-realization principle whose data can be
erased into v2.230.  In particular, it should expose:

- a selector-independent realization/certificate type for each residual value;
- a validity predicate or canonical certificate for realized residual-value
  codes;
- an extraction from valid realizations into `Fin 1296`;
- source-choice stability, or a distinguished valid realization whose code is
  definitionally the exported one;
- selected-admissible equality-reflection for residual values carrying
  `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` evidence
  from essential parents.

The bridge into v2.230 should then define
`residualValueCodeSource` as the realization/certificate carrier, use the
distinguished realization as `residualValueCodeSourceOfValue`, use the
realization validity predicate as `residualValueSource_valid`, and project the
realized code into `residualValueCodeOfSource`.

## Suggested Data Shape

A future no-sorry Lean interface can use a carrier along these lines:

```lean
structure
  PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealizationData
    {L : Nat} [NeZero L]
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) ->
        Finset (ConcretePlaquette physicalClayDimension L)) where
  residualValueCodeRealization :
    forall residual : Finset (ConcretePlaquette physicalClayDimension L),
      {q : ConcretePlaquette physicalClayDimension L // q in residual} -> Type

  residualValueCodeRealizationOfValue :
    forall residual
      (q : {q : ConcretePlaquette physicalClayDimension L // q in residual}),
      residualValueCodeRealization residual q

  residualValueCodeRealization_valid :
    forall residual
      (q : {q : ConcretePlaquette physicalClayDimension L // q in residual}),
      residualValueCodeRealization residual q -> Prop

  residualValueCodeRealizationOfValue_valid :
    forall residual
      (q : {q : ConcretePlaquette physicalClayDimension L // q in residual}),
      residualValueCodeRealization_valid residual q
        (residualValueCodeRealizationOfValue residual q)

  residualValueCodeOfRealization :
    forall residual
      (q : {q : ConcretePlaquette physicalClayDimension L // q in residual}),
      residualValueCodeRealization residual q -> Fin 1296

  residualValueCode_realization_ext :
    forall residual
      (q : {q : ConcretePlaquette physicalClayDimension L // q in residual})
      (s t : residualValueCodeRealization residual q),
      residualValueCodeRealization_valid residual q s ->
      residualValueCodeRealization_valid residual q t ->
      residualValueCodeOfRealization residual q s =
        residualValueCodeOfRealization residual q t

  selectorAdmissible_realizedCode_injective :
    forall residual
      (a b : {q : ConcretePlaquette physicalClayDimension L // q in residual}),
      (exists p : {p : ConcretePlaquette physicalClayDimension L //
          p in essential residual},
        Nonempty
          (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
            residual p.1 a)) ->
      (exists p : {p : ConcretePlaquette physicalClayDimension L //
          p in essential residual},
        Nonempty
          (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
            residual p.1 b)) ->
      residualValueCodeOfRealization residual a
          (residualValueCodeRealizationOfValue residual a) =
        residualValueCodeOfRealization residual b
          (residualValueCodeRealizationOfValue residual b) ->
      a.1 = b.1
```

The theorem should use the same v2.121 bookkeeping residual-fiber parameters
as the current chain: root, `k`, deleted vertex, `parentOf`, `essential`,
safe-deletion/bookkeeping evidence, the image characterization of
`essential residual`, and `essential residual ⊆ residual`.

## Expected Bridge

Given realization data, produce v2.230 source data by setting:

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

This bridge should be structural erasure/repackaging only.  All mathematical
content remains in the realization theorem.

## Rejected Routes

This scope does not authorize:

- selected-image cardinality;
- bounded menu cardinality;
- empirical search;
- `finsetCodeOfCardLe`;
- root-shell codes as residual-subtype bookkeeping/base-zone injectivity;
- local-neighbor codes as residual-subtype bookkeeping/base-zone injectivity;
- local-displacement codes as residual-subtype bookkeeping/base-zone
  injectivity;
- parent-relative `terminalNeighborCode` equality;
- deleted-X shortcut, i.e. treating deleted `X` as a residual terminal
  neighbor for `residual = X.erase (deleted X)`;
- the v2.161 selector-image cycle.

## Validation

- This dashboard note exists.
- It names the exact bridge into
  `PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296`.
- No Lean file was edited; no `lake build` was required for this
  dashboard-only scope.
- F3-COUNT remains `CONDITIONAL_BRIDGE`; no status, percentage, README metric,
  planner metric, ledger row, proof claim, or Clay-level claim moved.

## Next Task

```text
CODEX-F3-BASE-ZONE-RESIDUAL-VALUE-CODE-REALIZATION-INTERFACE-001
```

Add the no-sorry Lean Prop/interface and, only if it builds without `sorry`,
the bridge:

```lean
physicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296_of_baseZoneResidualValueCodeRealization1296
```
