# F3 bookkeeping base-zone tag coordinate interface v2.218

Task: `CODEX-F3-BOOKKEEPING-BASE-ZONE-TAG-COORDINATE-INTERFACE-001`

Status: `DONE_INTERFACE_AND_BRIDGE`

## Lean additions

Added the selector-independent coordinate carrier:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinateData
```

Added the upstream Prop/interface:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296
```

Added the no-sorry bridge into the v2.213 downstream tag-space source:

```lean
physicalPlaquetteGraphResidualFiberBookkeepingTagSpaceInjection1296_of_residualFiberBookkeepingBaseZoneTagCoordinate1296
```

The bridge target is exactly:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagSpaceInjection1296
```

## Interface shape

The new carrier exposes, for the v2.121 bookkeeping residual-fiber hypotheses:

- `baseZoneTagSpace` on each whole residual subtype;
- `baseZoneTagOfResidualValue` for every residual value, before any fixed
  selector, selected image, or bounded menu is supplied;
- `baseZoneTagIntoFin1296`;
- `selectedAdmissible_injective` for residual values carrying
  `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` evidence
  from essential parents.

The Prop returns a `Nonempty` instance of this coordinate carrier.  The bridge
then projects the tag space, residual-value extractor, `Fin 1296` encoding, and
selected-admissible injectivity law into
`PhysicalPlaquetteGraphResidualFiberBookkeepingTagSpaceInjection1296`.

## Rejected routes

The interface and bridge do not use or authorize selected-image cardinality,
bounded menu cardinality, empirical search, `finsetCodeOfCardLe`,
root-shell/local-neighbor/local-displacement codes as residual-subtype
bookkeeping tag injectivity, parent-relative `terminalNeighborCode` equality,
the deleted-X shortcut for `residual = X.erase (deleted X)`, or the v2.161
selector-image cycle.

## Validation

Command:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result: passed.

New theorem/interface axiom traces:

```text
PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinateData:
  [propext, Classical.choice, Quot.sound]

PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296:
  [propext, Classical.choice, Quot.sound]

physicalPlaquetteGraphResidualFiberBookkeepingTagSpaceInjection1296_of_residualFiberBookkeepingBaseZoneTagCoordinate1296:
  [propext, Classical.choice, Quot.sound]
```

F3-COUNT remains `CONDITIONAL_BRIDGE`.  No status, percentage, README metric,
planner metric, ledger row, proof claim beyond the Lean interface/bridge, or
Clay-level claim moved.

## Next task

```text
CODEX-F3-PROVE-BOOKKEEPING-BASE-ZONE-TAG-COORDINATE-001
```

Prove `PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296`
or reduce it to the next exact no-closure blocker.
