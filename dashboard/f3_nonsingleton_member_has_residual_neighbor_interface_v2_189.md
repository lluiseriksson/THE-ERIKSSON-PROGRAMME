# F3 Non-Singleton Residual Member Has Residual Neighbor Interface

Task: `CODEX-F3-NONSINGLETON-MEMBER-HAS-RESIDUAL-NEIGHBOR-INTERFACE-001`
Status: `DONE_INTERFACE_LANDED_NO_STATUS_MOVE`
Date: 2026-04-28T01:05:00Z

## Lean Interface

Codex added the no-sorry Prop/interface:

```lean
PhysicalPlaquetteGraphResidualFiberNonSingletonMemberHasResidualNeighbor1296
```

The interface is residual-local and neighbor-only.  Under the v2.121
bookkeeping residual-fiber hypotheses, for each anchored residual fiber and
essential parent `p`, a non-singleton residual must contain a residual vertex
`q` with:

```lean
p.1 ∈ (plaquetteGraph physicalClayDimension L).neighborFinset q.1
```

The witness `q` has subtype membership in the residual.  The deleted vertex of
a current witness is not used and cannot serve as a terminal neighbor for
`residual = X.erase (deleted X)`.

## Bridge Status

Exact downstream bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberNonSingletonMemberNeighborWalkSplit1296
```

No bridge theorem was added in this pass because the downstream walk-split
target is not yet present in Lean.  The intended bridge remains:

```lean
physicalPlaquetteGraphResidualFiberNonSingletonMemberNeighborWalkSplit1296_of_residualFiberNonSingletonMemberHasResidualNeighbor1296
```

That later bridge must combine this neighbor-only source with induced residual
walk data; this interface alone does not claim the full selector-data source.

## Deliberate Non-Routes

This interface does not claim:

- full `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`;
- source or target subtypes beyond the adjacent residual neighbor witness;
- induced residual walks or walk splitting;
- terminal-neighbor suffix data;
- selected-image cardinality;
- bounded menu cardinality;
- empirical search;
- `finsetCodeOfCardLe`;
- deleted-vertex adjacency outside the residual;
- the v2.161 selector-image cycle.

## Validation

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

passed.

The new axiom trace is:

```text
YangMills.PhysicalPlaquetteGraphResidualFiberNonSingletonMemberHasResidualNeighbor1296
depends on axioms: [propext, Classical.choice, Quot.sound]
```

F3-COUNT remains `CONDITIONAL_BRIDGE`; no status, percentage, README metric,
planner metric, ledger row, vacuity caveat, proof claim, or Clay-level claim
moved.
