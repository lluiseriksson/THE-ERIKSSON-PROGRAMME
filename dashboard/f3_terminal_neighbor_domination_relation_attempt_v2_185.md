# F3 residual terminal-neighbor domination relation proof attempt v2.185

Task: `CODEX-F3-PROVE-TERMINAL-NEIGHBOR-DOMINATION-RELATION-001`

Status: `DONE_NO_CLOSURE_SELECTOR_DATA_SOURCE_MISSING`

## Attempted target

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominationRelation1296
```

The target was not proved from the v2.121 bookkeeping residual-fiber
hypotheses.

The v2.184 interface and bridge still build:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominationRelation1296

physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296_of_residualFiberTerminalNeighborDominationRelation1296
```

These names correctly isolate the menu-free bridge into:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296
```

## What blocked Strategy A

Cowork's Strategy A proposed a structural lemma such as:

```lean
essential_parent_has_residual_neighbor
```

That lemma is not strong enough for the current Lean target.  The domination
relation does not merely need a residual neighbor of an essential parent.  It
must produce:

```lean
∃ q : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual},
  Nonempty
    (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
      residual p.1 q)
```

The existing selector-data record requires all of the following fields:

- `target : {r // r ∈ residual}` with `target_eq : target.1 = p`;
- `source : {s // s ∈ residual}`;
- an induced residual walk `canonicalWalk : source -> target`;
- an induced residual walk `prefixToTerminalNeighbor : source -> q`;
- an induced residual walk `terminalNeighborSuffix : q -> target`;
- final-edge adjacency `p ∈ neighborFinset q.1` when `residual.card ≠ 1`;
- a `terminalNeighborCode : Fin 1296`.

The v2.121 bookkeeping theorem supplies `deleted`, `parentOf`, `essential`,
the essential image identity, and `essential residual ⊆ residual`.  It also
uses deleted-vertex residual-parent facts in the direction needed to choose a
parent for a deleted vertex.  It does not supply, for each essential parent in
an arbitrary residual fiber, a residual terminal neighbor together with the
full induced-walk prefix/suffix selector package above.

## Exact no-closure blocker

The next missing theorem is a residual-local selector-data source, tentatively:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296
```

It should bridge into:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominationRelation1296
```

The source theorem must construct, from the v2.121 bookkeeping residual-fiber
hypotheses and without any cardinality compression, for every residual fiber and
essential parent:

```lean
∃ q : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual},
  Nonempty
    (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
      residual p.1 q)
```

To be a genuine improvement over merely restating the domination relation, the
source must identify the structural ingredients that build the selector-data
fields: residual membership of the target, a canonical residual source, induced
residual walks to both the parent and selected terminal neighbor, the
terminal-neighbor suffix, and the final-edge adjacency clause for non-singleton
residual fibers.

## Rejected non-routes

This attempt did not use:

- selected-image cardinality;
- bounded menu cardinality;
- `finsetCodeOfCardLe` on an already bounded selected image;
- the v2.161 cycle
  `SelectorImageBound -> SelectorCodeSeparation -> CodeSeparation ->
   DominatingMenu -> ImageCompression -> SelectorImageBound`;
- residual paths alone as proof of selector data;
- root-shell reachability alone as proof of selector data;
- local degree alone as proof of selector data;
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
axiom trace was introduced.  The already-landed v2.184 bridge retains the
canonical trace:

```text
[propext, Classical.choice, Quot.sound]
```

F3-COUNT remains `CONDITIONAL_BRIDGE`; no percentage, status, README metric,
planner metric, ledger row, or Clay-level claim moved.

## Next Codex task

```text
CODEX-F3-TERMINAL-NEIGHBOR-SELECTOR-DATA-SOURCE-SCOPE-001
```
