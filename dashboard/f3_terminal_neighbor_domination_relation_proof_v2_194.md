# v2.194 - Terminal-neighbor domination relation proof

**Task:** `CODEX-F3-PROVE-TERMINAL-NEIGHBOR-DOMINATION-RELATION-AFTER-SELECTOR-DATA-SOURCE-001`

## Lean Closure

Codex proved:

```lean
physicalPlaquetteGraphResidualFiberTerminalNeighborDominationRelation1296 :
  PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominationRelation1296
```

The proof is exactly the direct bridge application:

```lean
physicalPlaquetteGraphResidualFiberTerminalNeighborDominationRelation1296_of_residualFiberTerminalNeighborSelectorDataSource1296
  physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296
```

## Route

This closure uses the v2.193 selector-data source theorem as the complete
domination payload.  It does not reconstruct domination witnesses directly and
does not route through bounded menus or image cardinality.

## Validation

`lake build YangMills.ClayCore.LatticeAnimalCount` passed.

Targeted axiom traces:

```text
YangMills.physicalPlaquetteGraphResidualFiberTerminalNeighborDominationRelation1296
[propext, Classical.choice, Quot.sound]

YangMills.physicalPlaquetteGraphResidualFiberTerminalNeighborDominationRelation1296_of_residualFiberTerminalNeighborSelectorDataSource1296
[propext, Classical.choice, Quot.sound]
```

## Guardrails

The proof does not use selected-image cardinality, bounded menu cardinality,
empirical search, `finsetCodeOfCardLe`, deleted-vertex adjacency outside the
residual, or the v2.161 circular chain.

F3-COUNT remains `CONDITIONAL_BRIDGE`.  No status, percentage, README metric,
planner metric, ledger row, vacuity caveat, proof claim, or Clay-level claim
moved.

## Next Step

The downstream selector source should now close by applying:

```lean
physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296_of_residualFiberTerminalNeighborDominationRelation1296
  physicalPlaquetteGraphResidualFiberTerminalNeighborDominationRelation1296
```
