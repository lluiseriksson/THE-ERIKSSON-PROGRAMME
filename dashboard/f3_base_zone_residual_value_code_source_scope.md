# F3 Base-Zone Residual Value Code Source Scope

Task: `CODEX-F3-BASE-ZONE-RESIDUAL-VALUE-CODE-SOURCE-SCOPE-001`
Status: `DONE_SCOPE_DELIVERED_NO_LEAN_NO_STATUS_MOVE`
Timestamp: `2026-04-28T04:35:00Z`

## Proposed Upstream Theorem

Tentative Lean target:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296
```

Bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296
```

Expected bridge name:

```lean
physicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296_of_baseZoneResidualValueCodeSource1296
```

## Purpose

The v2.228 interface
`PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296`
already asks for a selector-independent residual-value code into `Fin 1296` on
the whole residual subtype and selected-admissible equality-reflection.  The
v2.229 proof attempt showed that this is still too direct for a proof attempt:
the current Lean API has no structural source explaining where such a code
comes from.

This scope therefore inserts a strictly upstream source layer.  It should
expose proof-relevant residual-value code source data before erasing that data
into the v2.228 code-injection interface.

## Why This Is Not A Restatement

The source theorem must not merely return
`PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjectionData`.
Instead it should provide:

- a selector-independent source/certificate type for each residual value;
- a canonical source witness for every value of the whole residual subtype;
- a code extraction from validated source witnesses into `Fin 1296`;
- a proof that the extracted code is independent of source-witness choices, or
  a distinguished source witness whose extracted code is used;
- selected-admissible equality-reflection for values carrying
  `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` evidence
  from essential parents.

The bridge into v2.228 then forgets the source/certificate layer and keeps only
the residual-value code plus selected-admissible equality-reflection.

## Suggested Data Shape

A future no-sorry Lean interface can use a carrier along these lines:

```lean
structure
  PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSourceData
    {L : Nat} [NeZero L]
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) ->
        Finset (ConcretePlaquette physicalClayDimension L)) where
  residualValueCodeSource :
    forall residual : Finset (ConcretePlaquette physicalClayDimension L),
      {q : ConcretePlaquette physicalClayDimension L // q in residual} -> Type

  residualValueCodeSourceOfValue :
    forall residual
      (q : {q : ConcretePlaquette physicalClayDimension L // q in residual}),
      residualValueCodeSource residual q

  residualValueSource_valid :
    forall residual
      (q : {q : ConcretePlaquette physicalClayDimension L // q in residual}),
      residualValueCodeSource residual q -> Prop

  residualValueCodeSourceOfValue_valid :
    forall residual
      (q : {q : ConcretePlaquette physicalClayDimension L // q in residual}),
      residualValueSource_valid residual q
        (residualValueCodeSourceOfValue residual q)

  residualValueCodeOfSource :
    forall residual
      (q : {q : ConcretePlaquette physicalClayDimension L // q in residual}),
      residualValueCodeSource residual q -> Fin 1296

  residualValueCode_source_ext :
    forall residual
      (q : {q : ConcretePlaquette physicalClayDimension L // q in residual})
      (s t : residualValueCodeSource residual q),
      residualValueSource_valid residual q s ->
      residualValueSource_valid residual q t ->
      residualValueCodeOfSource residual q s =
        residualValueCodeOfSource residual q t

  selectorAdmissible_sourceCode_injective :
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
      residualValueCodeOfSource residual a
          (residualValueCodeSourceOfValue residual a) =
        residualValueCodeOfSource residual b
          (residualValueCodeSourceOfValue residual b) ->
      a.1 = b.1
```

The theorem should use the same v2.121 bookkeeping residual-fiber parameters as
the v2.226-v2.228 lane: deleted vertex, `parentOf`, `essential`, safe-deletion
and bookkeeping evidence, the image characterization of `essential residual`,
and `essential residual ⊆ residual`.

## Expected Bridge

Given source data, define the v2.228 code by:

```lean
baseZoneOriginCertificateCode residual q :=
  residualValueCodeOfSource residual q
    (residualValueCodeSourceOfValue residual q)
```

Then prove `selectorAdmissible_code_injective` by applying
`selectorAdmissible_sourceCode_injective`.  If the eventual source interface
allows arbitrary valid witnesses instead of a distinguished witness,
`residualValueCode_source_ext` supplies the equality needed to normalize to the
distinguished code before applying the injectivity field.

## Rejected Routes

This scope does not authorize:

- selected-image cardinality;
- bounded menu cardinality;
- empirical search;
- `finsetCodeOfCardLe`;
- root-shell codes as residual-subtype bookkeeping/base-zone injectivity;
- local-neighbor codes as residual-subtype bookkeeping/base-zone injectivity;
- local-displacement codes as residual-subtype bookkeeping/base-zone injectivity;
- parent-relative `terminalNeighborCode` equality;
- deleted-X shortcut, i.e. treating deleted `X` as a residual terminal neighbor
  for `residual = X.erase (deleted X)`;
- the v2.161 cycle, including the v2.161 selector-image cycle.

## Validation

- This dashboard note exists.
- It names the exact bridge into
  `PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296`.
- No Lean file was edited; no `lake build` was required for this
  dashboard-only scope.
- F3-COUNT remains `CONDITIONAL_BRIDGE`; no status, percentage, README metric,
  planner metric, ledger row, proof claim, or Clay-level claim moved.

## Next Task

```text
CODEX-F3-BASE-ZONE-RESIDUAL-VALUE-CODE-SOURCE-INTERFACE-001
```

Add the no-sorry Lean Prop/interface and, only if it builds without `sorry`,
the bridge:

```lean
physicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296_of_baseZoneResidualValueCodeSource1296
```
