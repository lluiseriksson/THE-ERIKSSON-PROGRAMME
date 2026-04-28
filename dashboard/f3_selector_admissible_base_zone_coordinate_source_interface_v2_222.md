# F3 selector-admissible base-zone coordinate source interface v2.222

Task: `CODEX-F3-SELECTOR-ADMISSIBLE-BASE-ZONE-COORDINATE-SOURCE-INTERFACE-001`

Status: `DONE_INTERFACE_AND_BRIDGE_LANDED`

Date: 2026-04-28T01:15:00Z

## Lean additions

Added the proof-relevant source carrier:

```lean
PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSourceData
```

Location:

```text
YangMills/ClayCore/LatticeAnimalCount.lean:4047
```

Added the no-sorry Prop/interface:

```lean
PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296
```

Location:

```text
YangMills/ClayCore/LatticeAnimalCount.lean:4332
```

Added the structural erasure bridge:

```lean
physicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296_of_residualFiberSelectorAdmissibleBaseZoneCoordinateSource1296
```

Location:

```text
YangMills/ClayCore/LatticeAnimalCount.lean:4534
```

The bridge target is exactly:

```lean
PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296
```

## Interface shape

The new source data is not merely the v2.220 injection carrier renamed.  It adds
a proof-relevant realization layer:

```lean
baseZoneCoordinateRealizes :
  forall residual,
    {q : ConcretePlaquette physicalClayDimension L // q in residual} ->
      baseZoneCoordinateSpace residual -> Prop
```

and each residual value is assigned a realized coordinate:

```lean
baseZoneCoordinateOfResidualValue :
  forall residual
    (q : {q : ConcretePlaquette physicalClayDimension L // q in residual}),
      {c : baseZoneCoordinateSpace residual //
        baseZoneCoordinateRealizes residual q c}
```

The selected-admissible injectivity field consumes realization proofs for both
coordinates before using the `Fin 1296` encoding.  The bridge into the v2.220
injection interface erases these realization certificates and keeps only the
coordinate value, encoder, and induced injectivity law.

## Rejected routes

The interface and bridge do not use selected-image cardinality, bounded menu
cardinality, empirical search, `finsetCodeOfCardLe`, root-shell/local-neighbor/
local-displacement codes as residual-subtype bookkeeping/base-zone injectivity,
parent-relative `terminalNeighborCode` equality, the deleted-X shortcut for
`residual = X.erase (deleted X)`, or the v2.161 selector-image cycle.

## Validation

Command:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result: passed.

New theorem/interface axiom traces:

```text
PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSourceData:
  [propext, Classical.choice, Quot.sound]

PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296:
  [propext, Classical.choice, Quot.sound]

physicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296_of_residualFiberSelectorAdmissibleBaseZoneCoordinateSource1296:
  [propext, Classical.choice, Quot.sound]
```

F3-COUNT remains `CONDITIONAL_BRIDGE`.  No status, percentage, README metric,
planner metric, ledger row, proof claim beyond the Lean interface/bridge, or
Clay-level claim moved.

## Next task

```text
CODEX-F3-PROVE-SELECTOR-ADMISSIBLE-BASE-ZONE-COORDINATE-SOURCE-001
```

Prove
`PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296`
or reduce it to the next exact no-closure blocker.
