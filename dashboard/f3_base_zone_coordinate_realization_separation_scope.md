# F3 base-zone coordinate realization separation scope

Task: `CODEX-F3-BASE-ZONE-COORDINATE-REALIZATION-SEPARATION-SCOPE-001`

Status: `DONE_SCOPE_DELIVERED_NO_LEAN_NO_STATUS_MOVE`

## Proposed upstream theorem

Tentative Lean target:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296
```

This theorem should sit strictly upstream of:

```lean
PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296
```

and supply the latter by erasing proof-relevant residual bookkeeping/base-zone
realization certificates.

## Why this is not a restatement

The v2.222 source interface already contains a `baseZoneCoordinateRealizes`
relation and a realized coordinate for each residual value.  The new upstream
theorem must isolate the origin of those realizations: a selector-independent
bookkeeping/base-zone coordinate certificate source on the whole residual
subtype, before any fixed selector, selected image, or bounded menu is supplied.

The bridge into
`PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296`
should forget this origin/certificate layer and keep only the realized
coordinate, `Fin 1296` encoder, and selected-admissible injectivity law required
by `PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSourceData`.

This avoids merely renaming
`PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296`.

## Suggested realization data shape

A future no-sorry interface may introduce a carrier along these lines:

```lean
structure
  PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparationData
    {L : Nat} [NeZero L]
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) ->
        Finset (ConcretePlaquette physicalClayDimension L)) where
  baseZoneCoordinateSpace :
    forall residual : Finset (ConcretePlaquette physicalClayDimension L), Type

  baseZoneCoordinateOrigin :
    forall residual,
      {q : ConcretePlaquette physicalClayDimension L // q in residual} -> Type

  baseZoneCoordinateOfOrigin :
    forall residual
      (q : {q : ConcretePlaquette physicalClayDimension L // q in residual}),
        baseZoneCoordinateOrigin residual q ->
          baseZoneCoordinateSpace residual

  baseZoneCoordinateOriginOfResidualValue :
    forall residual
      (q : {q : ConcretePlaquette physicalClayDimension L // q in residual}),
        baseZoneCoordinateOrigin residual q

  baseZoneCoordinateIntoFin1296 :
    forall residual, baseZoneCoordinateSpace residual -> Fin 1296

  baseZoneCoordinateOrigin_realizes :
    forall residual
      (q : {q : ConcretePlaquette physicalClayDimension L // q in residual})
      (origin : baseZoneCoordinateOrigin residual q),
        Prop

  selectorAdmissible_origin_injective :
    forall residual
      (a b : {q : ConcretePlaquette physicalClayDimension L // q in residual})
      (oa : baseZoneCoordinateOrigin residual a)
      (ob : baseZoneCoordinateOrigin residual b),
      baseZoneCoordinateOrigin_realizes residual a oa ->
      baseZoneCoordinateOrigin_realizes residual b ob ->
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
      baseZoneCoordinateIntoFin1296 residual
          (baseZoneCoordinateOfOrigin residual a oa) =
        baseZoneCoordinateIntoFin1296 residual
          (baseZoneCoordinateOfOrigin residual b ob) ->
      a.1 = b.1
```

The final Lean shape can be adjusted, but the critical separation is:

- `baseZoneCoordinateOrigin` is proof-relevant coordinate realization evidence
  tied to the bookkeeping/base-zone structure;
- `baseZoneCoordinateOfOrigin` erases an origin certificate to the coordinate
  consumed by the v2.222 source data;
- `selectorAdmissible_origin_injective` proves selected-admissible separation
  at the origin/certificate level, not from a selected image or bounded menu.

## Expected theorem shape

The proposition should use the same v2.121 bookkeeping residual-fiber hypotheses
as the v2.222 source interface:

- `deleted` and `parentOf`;
- `essential`;
- the safe-deletion/bookkeeping choice hypothesis;
- the image characterization of `essential residual`;
- `essential residual ⊆ residual`.

It should conclude:

```lean
Nonempty
  (PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparationData
    (L := L) essential)
```

for each bookkeeping configuration.

## Exact bridge

Bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296
```

Expected bridge name:

```lean
physicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296_of_baseZoneCoordinateRealizationSeparation1296
```

Bridge shape:

1. assume
   `PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296`;
2. under the v2.121 bookkeeping hypotheses, obtain realization/separation data;
3. instantiate
   `PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSourceData`
   with:
   - `baseZoneCoordinateSpace`;
   - `baseZoneCoordinateRealizes residual q c` defined by existence of an origin
     whose erased coordinate is `c`;
   - `baseZoneCoordinateOfResidualValue residual q` obtained from
     `baseZoneCoordinateOriginOfResidualValue residual q`;
   - `baseZoneCoordinateIntoFin1296`;
4. prove `selectorAdmissible_realized_injective` by unpacking the two
   realization witnesses and applying `selectorAdmissible_origin_injective`;
5. return
   `PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296`.

## Non-circular route options

### Route A: direct bookkeeping/base-zone certificate

Define a residual-local certificate type directly from the bookkeeping/base-zone
structure.  Each residual value receives a certificate before any selector data
is fixed, and certificate-level equality of the `Fin 1296` encoding separates
selector-admissible values.

### Route B: ambient coordinate with residual certificate

Use an ambient bookkeeping/base-zone coordinate only if it comes with a residual
realization certificate and a proof that selector-admissible residual values are
separated by the `Fin 1296` encoding.  The coordinate must not be a root-shell,
local-neighbor, local-displacement, or parent-relative terminal-neighbor code.

### Route C: strengthen v2.121 bookkeeping output

Introduce a theorem showing that the v2.121 residual-fiber bookkeeping data
itself carries a base-zone realization certificate for every residual value.
This would make the v2.222 source data a genuine extraction from bookkeeping
rather than a post-hoc selector-image construction.

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
  `PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296`.
- No Lean file was edited; no `lake build` was required for this dashboard-only
  scope.
- F3-COUNT remains `CONDITIONAL_BRIDGE`; no status, percentage, README metric,
  planner metric, ledger row, proof claim, or Clay-level claim moved.

## Next task

```text
CODEX-F3-BASE-ZONE-COORDINATE-REALIZATION-SEPARATION-INTERFACE-001
```

Add a no-sorry Lean Prop/interface for
`PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296`
and, only if it builds without `sorry`, the bridge
`physicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296_of_baseZoneCoordinateRealizationSeparation1296`.
