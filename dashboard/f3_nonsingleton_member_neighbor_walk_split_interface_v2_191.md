# v2.191 - Non-singleton residual member neighbor walk-split interface

**Task:** `CODEX-F3-NONSINGLETON-MEMBER-NEIGHBOR-WALK-SPLIT-INTERFACE-AFTER-NEIGHBOR-001`

## Result

Codex added the no-sorry Lean interface:

    PhysicalPlaquetteGraphResidualFiberNonSingletonMemberNeighborWalkSplit1296

and the no-sorry structural bridge:

    physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296_of_residualFiberNonSingletonMemberNeighborWalkSplit1296

Bridge target:

    PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296

## Scope

The interface accepts the newly proved
`PhysicalPlaquetteGraphResidualFiberNonSingletonMemberHasResidualNeighbor1296`
as the only permitted final-edge residual adjacency source.  It does not treat
that neighbor theorem as full selector-data source.

The new premise still requires the downstream walk-split payload for each
essential residual parent: source and target residual subtypes, a residual
terminal neighbor, `terminalNeighborCode : Fin 1296`, induced residual walks
`source -> target`, `source -> terminalNeighbor`, and
`terminalNeighbor -> target`, plus non-singleton final-edge adjacency.

## Validation

`lake build YangMills.ClayCore.LatticeAnimalCount` passed.

Targeted axiom traces:

    YangMills.PhysicalPlaquetteGraphResidualFiberNonSingletonMemberNeighborWalkSplit1296
    [propext, Classical.choice, Quot.sound]

    YangMills.physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296_of_residualFiberNonSingletonMemberNeighborWalkSplit1296
    [propext, Classical.choice, Quot.sound]

## Next blocker

The remaining Lean blocker is to prove:

    PhysicalPlaquetteGraphResidualFiberNonSingletonMemberNeighborWalkSplit1296

That proof must supply the induced residual walk-split data.  It cannot use the
deleted vertex of the current witness as a residual terminal neighbor for
`residual = X.erase (deleted X)`, and it cannot use selected-image cardinality,
bounded menu cardinality, empirical search, `finsetCodeOfCardLe`, or the
v2.161 circular chain.

F3-COUNT remains `CONDITIONAL_BRIDGE`.  No percentage, status, README metric,
planner metric, ledger row, vacuity caveat, proof claim, or Clay-level claim
moved.
