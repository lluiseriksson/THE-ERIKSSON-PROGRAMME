# F3 terminal-neighbor selector source proof v2.195

Task: `CODEX-F3-PROVE-TERMINAL-NEIGHBOR-SELECTOR-SOURCE-AFTER-DOMINATION-RELATION-001`

## Result

Closed the selector-source theorem in Lean:

```lean
theorem physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296 :
    PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296
```

The proof is the direct bridge application:

```lean
physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296_of_residualFiberTerminalNeighborDominationRelation1296
  physicalPlaquetteGraphResidualFiberTerminalNeighborDominationRelation1296
```

This deliberately keeps the selector-source payload inside the v2.194
domination-relation theorem and existing bridge. It does not reconstruct
selector source data, and it does not use selected-image cardinality, bounded
menu cardinality, empirical search, deleted vertices outside the residual,
`finsetCodeOfCardLe`, or the v2.161 selector-image cycle.

## Validation

- `lake build YangMills.ClayCore.LatticeAnimalCount` passed.
- `#print axioms YangMills.physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296`
  reports `[propext, Classical.choice, Quot.sound]`.
- `#print axioms YangMills.physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296_of_residualFiberTerminalNeighborDominationRelation1296`
  reports `[propext, Classical.choice, Quot.sound]`.

## Next blocker

`PhysicalPlaquetteGraphResidualFiberBookkeepingTagMap1296` now has the
selector-source premise available. The remaining explicit Lean-side premise for
the v2.182 two-premise bridge is:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagCodeForSelector1296
```

Next task should prove or precisely fail that compatible bookkeeping-tag code
for the already-landed selector source, without selected-image cardinality or
the v2.161 circular route.

F3-COUNT remains `CONDITIONAL_BRIDGE`. No status, percentage, README metric,
planner metric, ledger row, vacuity caveat, proof claim, or Clay-level claim
moved.
