# F3 residual bookkeeping tag value-code source interface v2.198

Task: `CODEX-F3-RESIDUAL-BOOKKEEPING-TAG-VALUE-CODE-SOURCE-INTERFACE-001`

Status: `DONE_INTERFACE_AND_BRIDGE_LANDED_NO_STATUS_MOVE`

## Lean landing

Added the no-sorry interface:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueCodeSource1296
```

Location:

```text
YangMills/ClayCore/LatticeAnimalCount.lean:4092
```

The interface is relative to the v2.121 bookkeeping residual-fiber hypotheses
and a fixed residual-local `terminalNeighborOfParent` selector with
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` evidence. It
supplies:

- residual-subtype bookkeeping-tag code data on the whole residual fiber:
  `PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCodeData`;
- selected-value separation for the values chosen by the fixed selector.

The code is a residual-value code source before the selected terminal-neighbor
image is considered.

## Bridge landed

Added the no-sorry bridge:

```lean
physicalPlaquetteGraphResidualFiberBookkeepingTagCodeForSelector1296_of_residualFiberBookkeepingTagValueCodeSource1296
```

Location:

```text
YangMills/ClayCore/LatticeAnimalCount.lean:4158
```

Bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagCodeForSelector1296
```

The bridge only projects the `bookkeepingTagCode` field from the residual-value
code data and reuses the source separation proof. It does not construct a code
from selected-image cardinality or from parent-relative selector data.

## Explicit non-routes

This interface and bridge do not use:

- selected-image cardinality;
- bounded menu cardinality;
- empirical search;
- `finsetCodeOfCardLe`;
- the v2.161 selector-image cycle;
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
YangMills.PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueCodeSource1296:
  [propext, Classical.choice, Quot.sound]

YangMills.physicalPlaquetteGraphResidualFiberBookkeepingTagCodeForSelector1296_of_residualFiberBookkeepingTagValueCodeSource1296:
  [propext, Classical.choice, Quot.sound]
```

F3-COUNT remains `CONDITIONAL_BRIDGE`. No status, percentage, README metric,
planner metric, ledger row, vacuity caveat, proof claim, or Clay-level claim
moved.

## Next task

`CODEX-F3-PROVE-BOOKKEEPING-TAG-VALUE-CODE-SOURCE-001`

Prove `PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueCodeSource1296` or
reduce it to the next exact no-closure blocker.
