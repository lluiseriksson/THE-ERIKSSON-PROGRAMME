# F3 base-zone coordinate realization separation attempt v2.225

Task: `CODEX-F3-PROVE-BASE-ZONE-COORDINATE-REALIZATION-SEPARATION-001`

Status: `DONE_NO_CLOSURE_ORIGIN_CERTIFICATE_SOURCE_MISSING`

Date: 2026-04-28T02:45:00Z

## Target

Attempted target:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296
```

The target is the v2.224 interface theorem whose bridge is already available:

```lean
physicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296_of_baseZoneCoordinateRealizationSeparation1296
```

Bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296
```

## Result

No Lean proof was added.  The current Lean API does not construct the
selector-independent residual bookkeeping/base-zone origin/certificate data
required by:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparationData
```

In particular, the available artifacts supply interfaces and erasure bridges,
but not a concrete source for:

```lean
baseZoneCoordinateOrigin
baseZoneCoordinateOriginOfResidualValue
baseZoneCoordinateOrigin_realizes
baseZoneCoordinateIntoFin1296
selectorAdmissible_origin_injective
```

Using the v2.224 interface itself as evidence would be circular and was not
done.

## Exact no-closure blocker

The next missing source is a concrete selector-independent base-zone origin
certificate theorem, tentatively:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296
```

It should bridge into:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296
```

and must construct, from the v2.121 bookkeeping residual-fiber hypotheses,
actual residual base-zone origin/certificate data on the whole residual subtype,
an encoding into `Fin 1296`, and selected-admissible origin-level injectivity
for values carrying
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` evidence from
essential parents.

## Why existing candidates do not close it

- `PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparationData`
  is only the carrier to be constructed.
- `PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296`
  is only the Prop/interface target.
- The v2.224 bridge only erases origin certificates into the v2.222 source data;
  it does not create those certificates.
- The v2.220-v2.222 source/injection interfaces are downstream of the missing
  origin/certificate source.
- Root-shell, local-neighbor, and local-displacement code lemmas do not provide
  residual-subtype bookkeeping/base-zone injectivity.
- A code from residual subtype cardinality would require the forbidden
  selected-image/cardinality/menu/`finsetCodeOfCardLe` route or an unavailable
  structural residual-value injection into `Fin 1296`.

## Rejected routes

This attempt did not use selected-image cardinality, bounded menu cardinality,
empirical search, `finsetCodeOfCardLe`, root-shell codes, local-neighbor codes,
local-displacement codes, parent-relative `terminalNeighborCode` equality, the
deleted-X shortcut for `residual = X.erase (deleted X)`, or the v2.161
selector-image cycle.

## Validation

Command:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result: passed.

Relevant v2.224 axiom traces remain:

```text
PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparationData:
  [propext, Classical.choice, Quot.sound]

PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296:
  [propext, Classical.choice, Quot.sound]

physicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296_of_baseZoneCoordinateRealizationSeparation1296:
  [propext, Classical.choice, Quot.sound]
```

F3-COUNT remains `CONDITIONAL_BRIDGE`.  No status, percentage, README metric,
planner metric, ledger row, proof claim, or Clay-level claim moved.

## Next task

```text
CODEX-F3-BASE-ZONE-ORIGIN-CERTIFICATE-SOURCE-SCOPE-001
```

Scope the selector-independent base-zone origin/certificate source theorem and
its bridge into
`PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296`.
