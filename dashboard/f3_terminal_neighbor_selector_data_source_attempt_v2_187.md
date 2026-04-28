# F3 residual terminal-neighbor selector-data source proof attempt v2.187

Task: `CODEX-F3-PROVE-TERMINAL-NEIGHBOR-SELECTOR-DATA-SOURCE-001`

Status: `DONE_NO_CLOSURE_RESIDUAL_MEMBER_NEIGHBOR_WALK_SPLIT_MISSING`

## Attempted target

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296
```

The target was not proved from the v2.121 bookkeeping residual-fiber
hypotheses.

The existing v2.186 interface and bridge still build:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296

physicalPlaquetteGraphResidualFiberTerminalNeighborDominationRelation1296_of_residualFiberTerminalNeighborSelectorDataSource1296
```

The bridge target remains:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominationRelation1296
```

## What blocks closure

For each residual fiber and essential parent

```lean
p : {p // p ∈ essential residual}
```

the v2.121 bookkeeping data gives:

- `essential residual` as an image of `parentOf` over current witnesses
  satisfying `X.erase (deleted X) = residual`;
- `essential residual ⊆ residual`, hence `p.1 ∈ residual`;
- for a current witness `X`, the deleted vertex is adjacent to `parentOf X`
  in the non-singleton case.

That is not yet enough for
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296`.
The selector-data source needs a residual terminal neighbor and full induced
walk data:

- `source : {s // s ∈ residual}`;
- `target : {r // r ∈ residual}` with `target.1 = p.1`;
- `terminalNeighbor : {q // q ∈ residual}`;
- `terminalNeighborCode : Fin 1296`;
- an induced residual `canonicalWalk : source -> target`;
- an induced residual `prefixToTerminalNeighbor : source -> terminalNeighbor`;
- an induced residual `terminalNeighborSuffix : terminalNeighbor -> target`;
- final-edge adjacency from `terminalNeighbor` to `p.1` when
  `residual.card ≠ 1`.

The tempting v2.121 adjacency is the wrong direction for this theorem: it
exhibits the deleted vertex as adjacent to the parent, but the deleted vertex
is outside `residual = X.erase (deleted X)`.  It therefore cannot serve as the
required `terminalNeighbor : {q // q ∈ residual}`.

## Exact no-closure blocker

The next missing structural theorem should isolate residual induced-graph
walk splitting for essential parents, tentatively:

```lean
PhysicalPlaquetteGraphResidualFiberNonSingletonMemberNeighborWalkSplit1296
```

It should bridge into:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296
```

The intended theorem should prove, under the v2.121 bookkeeping residual-fiber
hypotheses, that for every residual fiber and essential parent:

- the singleton residual case can be discharged with `terminalNeighbor = p`
  and vacuous final-edge adjacency;
- the non-singleton residual case supplies a `q ∈ residual` adjacent to `p.1`;
- the induced residual graph supplies compatible walk data
  `source -> p`, `source -> q`, and `q -> p`.

This is sharper than residual-neighbor existence alone: the bridge must also
build the exact source/target subtypes and induced residual walk split needed
by `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`.

## Rejected non-routes

This attempt did not use:

- residual-neighbor existence alone as a proof of selector data;
- selected-image cardinality;
- bounded menu cardinality;
- `finsetCodeOfCardLe` on an already bounded selected image;
- the v2.161 cycle
  `SelectorImageBound -> SelectorCodeSeparation -> CodeSeparation ->
   DominatingMenu -> ImageCompression -> SelectorImageBound`;
- residual paths alone;
- root-shell reachability alone;
- local degree alone;
- residual size or raw frontier;
- deleted-vertex adjacency outside the residual;
- local displacement codes or parent-relative `terminalNeighborCode` equality;
- empirical bounded search;
- post-hoc terminal-neighbor choices from a current `(X, deleted X)` witness.

## Validation

Command:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result: passed.

No new theorem was added in this proof attempt, so no new theorem-specific
axiom trace was introduced.  The already-landed v2.186 bridge retains the
canonical trace:

```text
[propext, Classical.choice, Quot.sound]
```

F3-COUNT remains `CONDITIONAL_BRIDGE`; no percentage, status, README metric,
planner metric, ledger row, or Clay-level claim moved.

## Next Codex task

```text
CODEX-F3-RESIDUAL-FIBER-NONSINGLETON-MEMBER-NEIGHBOR-WALK-SPLIT-SCOPE-001
```
