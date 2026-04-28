# F3 residual-fiber bookkeeping tag map scope v2.178

Task: `CODEX-F3-RESIDUAL-FIBER-BOOKKEEPING-TAG-MAP-SCOPE-001`

Status: `DONE_SCOPE_DELIVERED_NO_LEAN_NO_STATUS_MOVE`

## Proposed Lean target

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagMap1296
```

This should be an upstream residual-local source theorem for:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCode1296
```

with intended bridge:

```lean
physicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCode1296_of_residualFiberBookkeepingTagMap1296
```

Bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCode1296
```

## Required payload

The theorem should use the same v2.121 bookkeeping residual-fiber inputs as the
bookkeeping-tag terminal-neighbor interface:

```lean
root k deleted parentOf essential hchoice himage hessential_subset
```

and expose three independent pieces of data:

1. a residual-local `terminalNeighborOfParent` selector;
2. selector evidence
   `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`;
3. a bookkeeping residual-value tag map

```lean
bookkeepingTagCode :
  ∀ residual,
    {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} →
      Fin 1296
```

together with selected-value separation:

```lean
∀ residual (p q : {p : ConcretePlaquette physicalClayDimension L //
    p ∈ essential residual}),
  bookkeepingTagCode residual (terminalNeighborOfParent residual p) =
    bookkeepingTagCode residual (terminalNeighborOfParent residual q) →
  (terminalNeighborOfParent residual p).1 =
    (terminalNeighborOfParent residual q).1
```

The map must live on the whole residual subtype before selected terminal
neighbors are read from it.  It is therefore a residual-value bookkeeping tag,
not a code manufactured from the selected terminal-neighbor image.

## Bridge shape

The bridge into
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCode1296`
should only repack the upstream payload:

- reuse `terminalNeighborOfParent`;
- reuse `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`;
- set

```lean
bookkeepingTagCodeData residual :=
  { bookkeepingTagCode := bookkeepingTagCode residual }
```

- reuse the selected-value separation theorem.

No selected-image cardinality, finite image coding, or later selector-image
compression should appear in the bridge.

## What this isolates from v2.121

The proved v2.121 theorem

```lean
physicalPlaquetteGraph_baseAwareTerminalPredecessorBookkeeping1296
```

constructs `deleted`, `parentOf`, `essential`, and proves the residual-fiber
image/subset bookkeeping clauses.  It does not yet name a residual-value tag
domain, does not give a map into `Fin 1296`, and does not prove injectivity or
selected-value separation for terminal-neighbor selections.

This scope therefore identifies the next proof burden as a structural
bookkeeping-tag theorem over the residual subtype, not another terminal-neighbor
image bound.

## Explicit non-routes

This scope does not use:

- selected-image cardinality;
- `finsetCodeOfCardLe` on an already bounded selected image;
- the v2.161 cycle
  `SelectorImageBound → SelectorCodeSeparation → CodeSeparation →
   DominatingMenu → ImageCompression → SelectorImageBound`;
- local displacement codes;
- parent-relative `terminalNeighborCode` equality;
- residual size, raw frontier, residual paths, root-shell reachability,
  deleted-vertex adjacency, local degree, or empirical search;
- post-hoc terminal-neighbor choices from a current witness.

## Validation

Dashboard-only scope.  No Lean file was edited and no lake build was required.

F3-COUNT remains `CONDITIONAL_BRIDGE`; no percentage, status, README metric,
planner metric, ledger row, vacuity caveat, or Clay-level claim moved.

## Next Codex task

`CODEX-F3-RESIDUAL-FIBER-BOOKKEEPING-TAG-MAP-INTERFACE-001`

Add the no-sorry Lean Prop/interface
`PhysicalPlaquetteGraphResidualFiberBookkeepingTagMap1296` and, only if it
builds without sorry, the repacking bridge into
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCode1296`.
