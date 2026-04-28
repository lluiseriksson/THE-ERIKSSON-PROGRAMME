# v2.192 - Non-singleton residual member neighbor walk-split proof

**Task:** `CODEX-F3-PROVE-NONSINGLETON-MEMBER-NEIGHBOR-WALK-SPLIT-001`

## Lean Closure

Codex proved:

```lean
physicalPlaquetteGraphResidualFiberNonSingletonMemberNeighborWalkSplit1296 :
  PhysicalPlaquetteGraphResidualFiberNonSingletonMemberNeighborWalkSplit1296
```

The already-landed bridge remains:

```lean
physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296_of_residualFiberNonSingletonMemberNeighborWalkSplit1296 :
  PhysicalPlaquetteGraphResidualFiberNonSingletonMemberNeighborWalkSplit1296 →
  PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296
```

## Construction

For each residual fiber and essential parent `p`, the proof sets
`source = target = p` as residual subtypes.

In the singleton residual case, it takes `terminalNeighbor = target`, uses
`SimpleGraph.Walk.nil` for all three induced walks, and discharges the
non-singleton final-edge clause by contradiction.

In the non-singleton residual case, it:

1. extracts a current witness `X` from the `essential = image parentOf` premise;
2. derives `2 ≤ k` from `p ∈ residual`, `residual.card ≠ 1`, and
   `residual = X.erase (deleted X)`;
3. uses the v2.121 bookkeeping choice premise to prove the residual belongs to
   `plaquetteGraphPreconnectedSubsetsAnchoredCard ... (k - 1)`;
4. calls
   `PhysicalPlaquetteGraphResidualFiberNonSingletonMemberHasResidualNeighbor1296`
   to obtain a residual `terminalNeighbor = q` with final-edge adjacency to
   `p`;
5. converts that adjacency into the induced one-edge walks
   `source -> terminalNeighbor` and `terminalNeighbor -> target`.

The terminal-neighbor code is the fixed `0 : Fin 1296`; this theorem does not
attempt selected-value separation.

## Validation

`lake build YangMills.ClayCore.LatticeAnimalCount` passed.

Targeted axiom traces:

```text
YangMills.physicalPlaquetteGraphResidualFiberNonSingletonMemberNeighborWalkSplit1296
[propext, Classical.choice, Quot.sound]

YangMills.physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296_of_residualFiberNonSingletonMemberNeighborWalkSplit1296
[propext, Classical.choice, Quot.sound]
```

## Guardrails

The proof does not use the deleted vertex as a residual terminal neighbor for
`residual = X.erase (deleted X)`.  It does not use selected-image cardinality,
bounded menu cardinality, empirical search, `finsetCodeOfCardLe`, or the
v2.161 circular chain.

F3-COUNT remains `CONDITIONAL_BRIDGE`.  No status, percentage, README metric,
planner metric, ledger row, vacuity caveat, proof claim, or Clay-level claim
moved.

## Next Step

The downstream selector-data source should now close by applying:

```lean
physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296_of_residualFiberNonSingletonMemberNeighborWalkSplit1296
  physicalPlaquetteGraphResidualFiberNonSingletonMemberNeighborWalkSplit1296
```
