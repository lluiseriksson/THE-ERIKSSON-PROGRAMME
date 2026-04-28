# F3 selector-admissible base-zone coordinate source scope

Task: `CODEX-F3-SELECTOR-ADMISSIBLE-BASE-ZONE-COORDINATE-SOURCE-SCOPE-001`

Status: `DONE_SCOPE_DELIVERED_NO_LEAN_NO_STATUS_MOVE`

Date: 2026-04-28T01:03:00Z

## Proposed upstream theorem

Tentative Lean target:

```lean
PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296
```

This theorem should sit strictly upstream of:

```lean
PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296
```

and supply the latter by structural erasure/repackaging.

## Why this is not a restatement

The v2.220 injection interface already asks for:

- a coordinate space;
- a residual-value coordinate extractor;
- an encoding into `Fin 1296`;
- selected-admissible injectivity.

The source theorem should add the missing origin layer: a proof-relevant
bookkeeping/base-zone coordinate realization relation or certificate tying each
coordinate to a residual value under the v2.121 bookkeeping residual-fiber
hypotheses.  The bridge to the v2.220 injection interface then forgets the
realization certificates and keeps only the coordinate extractor, encoder, and
injectivity law.

This avoids merely renaming
`PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296`.

## Suggested source data shape

A future no-sorry interface may introduce a carrier along these lines:

```lean
structure
  PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSourceData
    {L : Nat} [NeZero L]
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) ->
        Finset (ConcretePlaquette physicalClayDimension L)) where
  baseZoneCoordinateSpace :
    forall residual : Finset (ConcretePlaquette physicalClayDimension L), Type

  baseZoneCoordinateRealizes :
    forall residual,
      {q : ConcretePlaquette physicalClayDimension L // q in residual} ->
        baseZoneCoordinateSpace residual -> Prop

  baseZoneCoordinateOfResidualValue :
    forall residual
      (q : {q : ConcretePlaquette physicalClayDimension L // q in residual}),
        {c : baseZoneCoordinateSpace residual //
          baseZoneCoordinateRealizes residual q c}

  baseZoneCoordinateIntoFin1296 :
    forall residual, baseZoneCoordinateSpace residual -> Fin 1296

  selectorAdmissible_realized_injective :
    forall residual
      (a b : {q : ConcretePlaquette physicalClayDimension L // q in residual})
      (ca cb : baseZoneCoordinateSpace residual),
      baseZoneCoordinateRealizes residual a ca ->
      baseZoneCoordinateRealizes residual b cb ->
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
      baseZoneCoordinateIntoFin1296 residual ca =
        baseZoneCoordinateIntoFin1296 residual cb ->
      a.1 = b.1
```

The exact Lean syntax may be adjusted during the interface task, but the
important point is the `baseZoneCoordinateRealizes` layer: it is where a proof
must eventually connect v2.121 bookkeeping/base-zone structure to residual
values before any selector image or bounded menu is supplied.

## Expected source theorem shape

The source proposition should use the same v2.121 bookkeeping residual-fiber
hypotheses as the v2.220 injection interface:

- `deleted` and `parentOf`;
- `essential`;
- the safe-deletion/bookkeeping choice hypothesis;
- the image characterization of `essential residual`;
- `essential residual ⊆ residual`.

It should conclude:

```lean
Nonempty
  (PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSourceData
    (L := L) essential)
```

for each such bookkeeping configuration.

## Exact bridge

Bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296
```

Expected bridge name:

```lean
physicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296_of_residualFiberSelectorAdmissibleBaseZoneCoordinateSource1296
```

Bridge shape:

1. assume
   `PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296`;
2. under the v2.121 bookkeeping hypotheses, obtain source data;
3. instantiate
   `PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjectionData`
   with:
   - `baseZoneCoordinateSpace`;
   - `(baseZoneCoordinateOfResidualValue residual q).1`;
   - `baseZoneCoordinateIntoFin1296`;
4. prove `selectorAdmissible_injective` by applying
   `selectorAdmissible_realized_injective` to the realization proofs
   `(baseZoneCoordinateOfResidualValue residual a).2` and
   `(baseZoneCoordinateOfResidualValue residual b).2`;
5. return
   `PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296`.

## Non-circular route options

### Route A: primitive base-zone realization relation

Define a residual-local base-zone realization relation directly from future
bookkeeping/base-zone geometry.  The source theorem proves every residual
value has a realized coordinate and that realized coordinates separate
selector-admissible residual values.

### Route B: v2.121 bookkeeping-to-coordinate extractor

Strengthen the v2.121 bookkeeping output with a theorem showing that the
`deleted`/`parentOf`/`essential` residual-fiber structure carries a
selector-independent coordinate certificate for every residual value.  This
would make the source data a genuine extraction from bookkeeping rather than a
post-hoc selected image.

### Route C: ambient base-zone coordinate with residual realization proof

Use an ambient/base-zone coordinate function on plaquettes, but require a
residual realization proof showing that selector-admissible residual values are
separated by its `Fin 1296` encoding in the relevant residual fiber.  This is
valid only if the ambient coordinate is a true bookkeeping/base-zone coordinate,
not a root-shell, local-neighbor, local-displacement, or parent-relative
terminal-neighbor code.

## Rejected routes

This scope does not use or authorize:

- selected-image cardinality;
- bounded menu cardinality;
- empirical search;
- `finsetCodeOfCardLe`;
- root-shell codes as residual-subtype bookkeeping/base-zone injectivity;
- local-neighbor codes as residual-subtype bookkeeping/base-zone injectivity;
- local-displacement codes as residual-subtype bookkeeping/base-zone
  injectivity;
- parent-relative `terminalNeighborCode` equality;
- treating deleted `X` as a residual terminal neighbor for
  `residual = X.erase (deleted X)`;
- the v2.161 selector-image cycle.

## Validation

- This dashboard scope note exists.
- The artifact names the exact bridge into
  `PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296`.
- No Lean file was edited; no `lake build` was required for this dashboard-only
  scope.
- F3-COUNT remains `CONDITIONAL_BRIDGE`; no status, percentage, README metric,
  planner metric, ledger row, proof claim, or Clay-level claim moved.

## Next task

```text
CODEX-F3-SELECTOR-ADMISSIBLE-BASE-ZONE-COORDINATE-SOURCE-INTERFACE-001
```

Add a no-sorry Lean Prop/interface for
`PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296`
and, only if it builds without `sorry`, the bridge
`physicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296_of_residualFiberSelectorAdmissibleBaseZoneCoordinateSource1296`.
