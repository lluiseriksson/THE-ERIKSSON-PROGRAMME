# F3 base-zone origin certificate source scope

Task: `CODEX-F3-BASE-ZONE-ORIGIN-CERTIFICATE-SOURCE-SCOPE-001`

Status: `DONE_SCOPE_DELIVERED_NO_LEAN_NO_STATUS_MOVE`

Date: 2026-04-28T03:00:00Z

## Proposed upstream theorem

Tentative Lean target:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296
```

This theorem should sit strictly upstream of:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296
```

and supply that theorem by converting concrete residual bookkeeping/base-zone
origin certificates into the v2.224 realization/separation data.

## Why this is not a restatement

`PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296`
already asks for a `baseZoneCoordinateOrigin` type, a realized origin for each
residual value, a coordinate encoder into `Fin 1296`, and origin-level
selected-admissible injectivity.

The new source theorem must isolate where those origins come from.  It should
expose a concrete certificate/provenance layer generated from the v2.121
bookkeeping residual-fiber hypotheses before erasing it into the v2.224
`baseZoneCoordinateOrigin` field.  In particular, it must provide a certificate
source tied to residual bookkeeping/base-zone structure, not merely rename
`baseZoneCoordinateOrigin`.

## Suggested source data shape

A future no-sorry interface may introduce a carrier along these lines:

```lean
structure
  PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSourceData
    {L : Nat} [NeZero L]
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) ->
        Finset (ConcretePlaquette physicalClayDimension L)) where
  baseZoneCoordinateSpace :
    forall residual : Finset (ConcretePlaquette physicalClayDimension L), Type

  baseZoneOriginCertificate :
    forall residual,
      {q : ConcretePlaquette physicalClayDimension L // q in residual} -> Type

  baseZoneOriginCertificateSource :
    forall residual
      (q : {q : ConcretePlaquette physicalClayDimension L // q in residual}),
        Type

  baseZoneOriginCertificateOfSource :
    forall residual
      (q : {q : ConcretePlaquette physicalClayDimension L // q in residual}),
        baseZoneOriginCertificateSource residual q ->
          baseZoneOriginCertificate residual q

  baseZoneOriginSourceOfResidualValue :
    forall residual
      (q : {q : ConcretePlaquette physicalClayDimension L // q in residual}),
        baseZoneOriginCertificateSource residual q

  baseZoneOriginSource_valid :
    forall residual
      (q : {q : ConcretePlaquette physicalClayDimension L // q in residual})
      (source : baseZoneOriginCertificateSource residual q),
        Prop

  baseZoneOriginCertificate_realizes :
    forall residual
      (q : {q : ConcretePlaquette physicalClayDimension L // q in residual})
      (cert : baseZoneOriginCertificate residual q),
        Prop

  baseZoneOriginCertificateOfSource_realizes :
    forall residual
      (q : {q : ConcretePlaquette physicalClayDimension L // q in residual})
      (source : baseZoneOriginCertificateSource residual q),
        baseZoneOriginSource_valid residual q source ->
        baseZoneOriginCertificate_realizes residual q
          (baseZoneOriginCertificateOfSource residual q source)

  baseZoneCoordinateOfCertificate :
    forall residual
      (q : {q : ConcretePlaquette physicalClayDimension L // q in residual}),
        baseZoneOriginCertificate residual q ->
          baseZoneCoordinateSpace residual

  baseZoneCoordinateIntoFin1296 :
    forall residual, baseZoneCoordinateSpace residual -> Fin 1296

  selectorAdmissible_certificate_injective :
    forall residual
      (a b : {q : ConcretePlaquette physicalClayDimension L // q in residual})
      (ca : baseZoneOriginCertificate residual a)
      (cb : baseZoneOriginCertificate residual b),
      baseZoneOriginCertificate_realizes residual a ca ->
      baseZoneOriginCertificate_realizes residual b cb ->
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
          (baseZoneCoordinateOfCertificate residual a ca) =
        baseZoneCoordinateIntoFin1296 residual
          (baseZoneCoordinateOfCertificate residual b cb) ->
      a.1 = b.1
```

The final Lean shape can be adjusted, but the critical separation is:

- `baseZoneOriginCertificateSource` is the concrete provenance layer from
  residual bookkeeping/base-zone data;
- `baseZoneOriginCertificateOfSource` erases provenance into the certificate
  consumed by the v2.224 origin layer;
- `baseZoneOriginCertificateOfSource_realizes` proves that a sourced
  certificate is valid for the residual value;
- `selectorAdmissible_certificate_injective` proves separation at certificate
  level, before any selected image, bounded menu, or `finsetCodeOfCardLe`
  construction is supplied.

## Expected theorem shape

The proposition should reuse the same v2.121 bookkeeping residual-fiber
hypotheses as the v2.224 realization/separation interface:

- `deleted` and `parentOf`;
- `essential`;
- the safe-deletion/bookkeeping choice hypothesis;
- the image characterization of `essential residual`;
- `essential residual ⊆ residual`.

It should conclude:

```lean
Nonempty
  (PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSourceData
    (L := L) essential)
```

for each bookkeeping configuration.

## Exact bridge

Bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296
```

Expected bridge name:

```lean
physicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296_of_baseZoneOriginCertificateSource1296
```

Bridge shape:

1. assume
   `PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296`;
2. under the v2.121 bookkeeping hypotheses, obtain certificate-source data;
3. instantiate
   `PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparationData`
   with:
   - `baseZoneCoordinateSpace`;
   - `baseZoneCoordinateOrigin residual q := baseZoneOriginCertificate residual q`;
   - `baseZoneCoordinateOfOrigin := baseZoneCoordinateOfCertificate`;
   - `baseZoneCoordinateOrigin_realizes := baseZoneOriginCertificate_realizes`;
   - `baseZoneCoordinateOriginOfResidualValue residual q` obtained from
     `baseZoneOriginSourceOfResidualValue residual q`,
     `baseZoneOriginCertificateOfSource`, and
     `baseZoneOriginCertificateOfSource_realizes`;
   - `baseZoneCoordinateIntoFin1296`;
4. prove `selectorAdmissible_origin_injective` by applying
   `selectorAdmissible_certificate_injective`;
5. return
   `PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296`.

## Non-circular source routes

### Route A: direct residual bookkeeping certificate

Define a certificate type directly from the v2.121 residual bookkeeping data.
The proof must show every residual value has such a certificate and that equal
`Fin 1296` certificate codes separate selector-admissible residual values.

### Route B: base-zone provenance plus erased coordinate

Expose a certificate source with explicit provenance data, then erase the
provenance to a coordinate.  The source proof must include a realization lemma
for each erased certificate and a selected-admissible injectivity lemma at the
certificate level.

### Route C: structural invariant from essential-parent bookkeeping

Strengthen the residual-fiber bookkeeping theorem with an invariant saying that
values that can carry terminal-neighbor selector data from essential parents
are separated by a selector-independent base-zone certificate.  This route
still must construct certificates on the whole residual subtype; it cannot
construct only selected-image codes.

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
  `PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296`.
- No Lean file was edited; no `lake build` was required for this dashboard-only
  scope.
- F3-COUNT remains `CONDITIONAL_BRIDGE`; no status, percentage, README metric,
  planner metric, ledger row, proof claim, or Clay-level claim moved.

## Next task

```text
CODEX-F3-BASE-ZONE-ORIGIN-CERTIFICATE-SOURCE-INTERFACE-001
```

Add a no-sorry Lean Prop/interface for
`PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296` and,
only if it builds without `sorry`, the bridge
`physicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296_of_baseZoneOriginCertificateSource1296`.
