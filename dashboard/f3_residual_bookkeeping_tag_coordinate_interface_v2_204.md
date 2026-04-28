# F3 residual bookkeeping tag coordinate interface v2.204

Task: `CODEX-F3-RESIDUAL-BOOKKEEPING-TAG-COORDINATE-INTERFACE-001`

Status: `DONE_INTERFACE_AND_BRIDGE_LANDED_NO_STATUS_MOVE`

## Lean landing

Added the no-sorry coordinate-first interface:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagCoordinate1296
```

Location:

```text
YangMills/ClayCore/LatticeAnimalCount.lean:4092
```

The interface is relative to the v2.121 bookkeeping residual-fiber hypotheses.
It first produces residual-indexed bookkeeping/base-zone tag data:

```lean
forall residual,
  PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCodeData
    residual
```

Only after that coordinate data is supplied does it quantify over a fixed
`terminalNeighborOfParent` selector and selector evidence, then require
selected-value separation for that fixed selector.  This preserves the
coordinate-first source order scoped in v2.203.

## Bridge landed

Added the no-sorry bridge:

```lean
physicalPlaquetteGraphResidualFiberBookkeepingTagValueSeparation1296_of_residualFiberBookkeepingTagCoordinate1296
```

Location:

```text
YangMills/ClayCore/LatticeAnimalCount.lean:4230
```

Bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueSeparation1296
```

The bridge is direct repackaging: it applies the coordinate source to the
v2.121 bookkeeping hypotheses, obtains `bookkeepingTagCodeData`, and passes the
coordinate separation clause through after the caller supplies the fixed
selector and evidence.

## Explicit non-routes

This interface and bridge do not use:

- selected-image cardinality;
- bounded menu cardinality;
- empirical search;
- `finsetCodeOfCardLe`;
- the v2.161 selector-image cycle;
- root-shell codes as residual-subtype tag injectivity;
- local neighbor codes as residual-subtype tag injectivity;
- local displacement codes;
- parent-relative `terminalNeighborCode` equality;
- deleted `X` as a residual terminal neighbor for
  `residual = X.erase (deleted X)`.

## Validation

Command:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result: passed.

The new `#print axioms` traces are:

```text
YangMills.PhysicalPlaquetteGraphResidualFiberBookkeepingTagCoordinate1296:
  [propext, Classical.choice, Quot.sound]

YangMills.physicalPlaquetteGraphResidualFiberBookkeepingTagValueSeparation1296_of_residualFiberBookkeepingTagCoordinate1296:
  [propext, Classical.choice, Quot.sound]
```

F3-COUNT remains `CONDITIONAL_BRIDGE`. No status, percentage, README metric,
planner metric, ledger row, vacuity caveat, proof claim, or Clay-level claim
moved.

## Next task

`CODEX-F3-PROVE-BOOKKEEPING-TAG-COORDINATE-001`

Prove `PhysicalPlaquetteGraphResidualFiberBookkeepingTagCoordinate1296` or
reduce it to the next exact no-closure blocker.
