# v2.193 - Terminal-neighbor selector-data source proof

**Task:** `CODEX-F3-PROVE-TERMINAL-NEIGHBOR-SELECTOR-DATA-SOURCE-AFTER-WALK-SPLIT-001`

## Lean Closure

Codex proved:

```lean
physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296 :
  PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296
```

The proof is exactly the direct bridge application:

```lean
physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296_of_residualFiberNonSingletonMemberNeighborWalkSplit1296
  physicalPlaquetteGraphResidualFiberNonSingletonMemberNeighborWalkSplit1296
```

## Route

This closure uses the v2.192 walk-split theorem as the complete source of the
selector-data payload.  It does not reconstruct selector data from residual
neighbor existence alone.

The selector-data source fields therefore come through the walk-split proof:
source and target residual subtypes, residual terminal neighbor,
`terminalNeighborCode : Fin 1296`, induced residual walks
`source -> target`, `source -> terminalNeighbor`, and
`terminalNeighbor -> target`, plus non-singleton final-edge adjacency.

## Validation

`lake build YangMills.ClayCore.LatticeAnimalCount` passed.

Targeted axiom traces:

```text
YangMills.physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296
[propext, Classical.choice, Quot.sound]

YangMills.physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296_of_residualFiberNonSingletonMemberNeighborWalkSplit1296
[propext, Classical.choice, Quot.sound]
```

## Guardrails

The proof does not use deleted-vertex adjacency outside the residual, selected
image cardinality, bounded menu cardinality, empirical search,
`finsetCodeOfCardLe`, or the v2.161 circular chain.

F3-COUNT remains `CONDITIONAL_BRIDGE`.  No status, percentage, README metric,
planner metric, ledger row, vacuity caveat, proof claim, or Clay-level claim
moved.

## Next Step

The downstream domination relation should now close by applying:

```lean
physicalPlaquetteGraphResidualFiberTerminalNeighborDominationRelation1296_of_residualFiberTerminalNeighborSelectorDataSource1296
  physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296
```
