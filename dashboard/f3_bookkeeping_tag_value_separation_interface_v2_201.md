# F3 bookkeeping tag value-separation interface v2.201

Task: `CODEX-F3-BOOKKEEPING-TAG-VALUE-SEPARATION-INTERFACE-001`

Status: `DONE_INTERFACE_AND_BRIDGE_LANDED_NO_STATUS_MOVE`

## Lean landing

Added the no-sorry interface:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueSeparation1296
```

Location:

```text
YangMills/ClayCore/LatticeAnimalCount.lean:4093
```

The interface is relative to the v2.121 bookkeeping residual-fiber hypotheses
and a fixed residual-local `terminalNeighborOfParent` selector with
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` evidence. It
exposes:

- residual-value bookkeeping/base-zone tag code data on the whole residual
  subtype via
  `PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCodeData`;
- selected-value separation for the terminal-neighbor values chosen by the
  fixed selector.

The code is required before restricting to the selected terminal-neighbor
image.

## Bridge landed

Added the no-sorry bridge:

```lean
physicalPlaquetteGraphResidualFiberBookkeepingTagValueCodeSource1296_of_residualFiberBookkeepingTagValueSeparation1296
```

Location:

```text
YangMills/ClayCore/LatticeAnimalCount.lean:4230
```

Bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueCodeSource1296
```

The bridge is direct repackaging from the value-separation interface into the
v2.198 value-code source interface.

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
YangMills.PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueSeparation1296:
  [propext, Classical.choice, Quot.sound]

YangMills.physicalPlaquetteGraphResidualFiberBookkeepingTagValueCodeSource1296_of_residualFiberBookkeepingTagValueSeparation1296:
  [propext, Classical.choice, Quot.sound]
```

F3-COUNT remains `CONDITIONAL_BRIDGE`. No status, percentage, README metric,
planner metric, ledger row, vacuity caveat, proof claim, or Clay-level claim
moved.

## Next task

`CODEX-F3-PROVE-BOOKKEEPING-TAG-VALUE-SEPARATION-001`

Prove `PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueSeparation1296` or
reduce it to the next exact no-closure blocker.
