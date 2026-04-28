# F3 Non-Singleton Residual Member Has Residual Neighbor Scope

Task: `CODEX-F3-NONSINGLETON-MEMBER-HAS-RESIDUAL-NEIGHBOR-SCOPE-001`
Status: `DONE_SCOPE_DELIVERED_NO_LEAN_NO_STATUS_MOVE`
Date: 2026-04-28T00:58:00Z

## Proposed Lean Target

Tentative theorem/interface:

```lean
PhysicalPlaquetteGraphResidualFiberNonSingletonMemberHasResidualNeighbor1296
```

The target should supply only the final-edge residual adjacency piece needed by
the downstream walk-split theorem:

```lean
PhysicalPlaquetteGraphResidualFiberNonSingletonMemberNeighborWalkSplit1296
```

It should not claim the full
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` package and
should not construct the induced residual walk split by itself.

## Minimal Statement Shape

The reusable graph lemma should first be stated independently of selector-image
or menu data:

```lean
-- Generic graph-animal form, suggested name.
plaquetteGraphPreconnectedSubsetsAnchoredCard_nonSingleton_member_has_neighbor
    {d L k : Nat} [NeZero d] [NeZero L]
    {root p : ConcretePlaquette d L}
    {residual : Finset (ConcretePlaquette d L)}
    (hresidual :
      residual ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k)
    (hp : p ∈ residual)
    (hnonSingleton : residual.card ≠ 1) :
    ∃ q, q ∈ residual ∧
      p ∈ (plaquetteGraph d L).neighborFinset q
```

The physical F3 wrapper can then specialize `d = physicalClayDimension` and
thread the v2.121 bookkeeping residual-fiber hypotheses:

```lean
PhysicalPlaquetteGraphResidualFiberNonSingletonMemberHasResidualNeighbor1296 :
  Prop
```

For each residual and each essential parent `p : {p // p ∈ essential residual}`,
it should use `hessential_subset residual p.2` to obtain `p.1 ∈ residual` and,
under `residual.card ≠ 1`, produce:

```lean
∃ q : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual},
  p.1 ∈ (plaquetteGraph physicalClayDimension L).neighborFinset q.1
```

## Bridge Into Walk-Split

Exact downstream bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberNonSingletonMemberNeighborWalkSplit1296
```

Suggested bridge name:

```lean
physicalPlaquetteGraphResidualFiberNonSingletonMemberNeighborWalkSplit1296_of_residualFiberNonSingletonMemberHasResidualNeighbor1296
```

The bridge should combine:

1. the new non-singleton residual-neighbor witness above;
2. existing induced reachability/path tools such as
   `plaquetteGraphPreconnectedSubsetsAnchoredCard_root_reachable` and
   `plaquetteGraphPreconnectedSubsetsAnchoredCard_root_exists_induced_path`;
3. the already-scoped singleton case where final-edge adjacency is vacuous.

The bridge still has to build source/target subtypes and induced walks. That
work belongs to the walk-split theorem, not to this neighbor-only source.

## Lean Route

The likely proof route for the generic lemma is:

1. From `hresidual`, recover induced preconnectedness via
   `plaquetteGraphPreconnectedSubsetsAnchoredCard_preconnected`.
2. From `hp : p ∈ residual` and `residual.card ≠ 1`, prove there is some
   `y ∈ residual` with `y ≠ p`. This is a finite-set non-singleton lemma, not a
   selected-image cardinality argument.
3. Use induced preconnectedness to get a walk in
   `(plaquetteGraph d L).induce {x | x ∈ residual}` from `p` to `y`.
4. Apply `simpleGraph_walk_exists_adj_start_of_ne` or
   `simpleGraph_walk_exists_adj_start_and_tail_of_ne` to extract the first
   adjacent residual vertex.
5. Project induced adjacency back to ambient plaquette adjacency with
   `SimpleGraph.induce_adj.mp`, then convert it to the desired
   `neighborFinset` orientation.

This is the same structural pattern already used for
`plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_root_neighbor`, but with
an arbitrary residual member `p` in place of the anchored `root`.

## Distinctions And Non-Routes

This target is not:

- deleted-vertex adjacency outside the residual;
- residual paths alone as selector data;
- residual size as a selected-image bound;
- selected-image cardinality;
- bounded menu cardinality;
- empirical search;
- `finsetCodeOfCardLe` on an already bounded selected image;
- local displacement coding or parent-relative `terminalNeighborCode` equality;
- the v2.161 cycle
  `SelectorImageBound -> SelectorCodeSeparation -> CodeSeparation ->
   DominatingMenu -> ImageCompression -> SelectorImageBound`.

The deleted vertex from a current witness is explicitly excluded: for
`residual = X.erase (deleted X)`, the deleted vertex is outside the residual and
cannot be used as the residual terminal neighbor.

## Validation

No Lean file was edited for this scope note, so no `lake build` was required.
The artifact names the bridge into
`PhysicalPlaquetteGraphResidualFiberNonSingletonMemberNeighborWalkSplit1296`
and keeps the obligation strictly at residual-member neighbor existence.

F3-COUNT remains `CONDITIONAL_BRIDGE`; no status, percentage, README metric,
planner metric, ledger row, vacuity caveat, proof claim, or Clay-level claim
moved.
