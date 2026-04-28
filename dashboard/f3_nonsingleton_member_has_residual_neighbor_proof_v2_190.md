# F3 Non-Singleton Residual Member Has Residual Neighbor Proof

Task: `CODEX-F3-PROVE-NONSINGLETON-MEMBER-HAS-RESIDUAL-NEIGHBOR-001`
Status: `DONE_PROVED_NO_STATUS_MOVE`
Date: 2026-04-28T01:20:00Z

## Lean Closure

Codex proved the neighbor-only source:

```lean
physicalPlaquetteGraphResidualFiberNonSingletonMemberHasResidualNeighbor1296 :
  PhysicalPlaquetteGraphResidualFiberNonSingletonMemberHasResidualNeighbor1296
```

The proof is supported by two new generic graph-animal lemmas:

```lean
plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_ne_member
plaquetteGraphPreconnectedSubsetsAnchoredCard_nonSingleton_member_has_neighbor
```

The generic route is:

1. use `residual.card ≠ 1` and `p ∈ residual` to find another residual member
   different from `p`;
2. use `plaquetteGraphPreconnectedSubsetsAnchoredCard_preconnected` to get an
   induced residual walk from `p` to that other member;
3. use `simpleGraph_walk_exists_adj_start_of_ne` to extract the first adjacent
   vertex of the walk;
4. project induced adjacency back to the ambient plaquette graph and convert it
   to the requested `neighborFinset` orientation.

The physical theorem then specializes this generic lemma to
`physicalClayDimension` and uses only `essential residual ⊆ residual` to place
the essential parent inside the residual.

## What This Does Not Prove

This closes only the residual-member neighbor source.  It does not claim:

- full `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`;
- induced residual walk splitting;
- source-to-parent, source-to-terminalNeighbor, or terminalNeighbor-to-parent
  walks;
- menu or selected-image cardinality;
- an empirical search result;
- `finsetCodeOfCardLe`;
- the v2.161 selector-image cycle.

The deleted vertex from a current witness is not used; the neighbor witness is
a subtype member of the residual itself.

## Validation

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

passed.

The new theorem axiom traces are no larger than:

```text
[propext, Classical.choice, Quot.sound]
```

## Next Blocker

The next downstream target remains:

```lean
PhysicalPlaquetteGraphResidualFiberNonSingletonMemberNeighborWalkSplit1296
```

That theorem must add the induced residual walk-split data needed by
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296`.

F3-COUNT remains `CONDITIONAL_BRIDGE`; no status, percentage, README metric,
planner metric, ledger row, vacuity caveat, proof claim, or Clay-level claim
moved.
