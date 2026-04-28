# F3 residual-fiber bookkeeping tag map proof attempt v2.180

Task: `CODEX-F3-PROVE-RESIDUAL-FIBER-BOOKKEEPING-TAG-MAP-001`

Status: `DONE_NO_CLOSURE_TERMINAL_NEIGHBOR_SELECTOR_SOURCE_MISSING`

## Lean target attempted

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagMap1296
```

No Lean theorem was added.

## Exact no-closure blocker

The v2.179 interface has four load-bearing pieces:

1. a residual-local `terminalNeighborOfParent` selector;
2. selector evidence
   `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`;
3. a residual-subtype bookkeeping tag map

```lean
∀ residual,
  {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} →
    Fin 1296
```

4. selected-value separation for the chosen terminal-neighbor values.

The current proved v2.121 theorem

```lean
physicalPlaquetteGraph_baseAwareTerminalPredecessorBookkeeping1296
```

only supplies the total bookkeeping functions `deleted`, `parentOf`,
`essential`, plus residual-fiber image and subset clauses.  It does not
construct a terminal-neighbor selector, does not construct
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`, and does not
construct a residual-value tag map.

The immediate upstream blocker is therefore a non-circular residual-local
terminal-neighbor selector source, tentatively:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296
```

with an intended bridge into the selector part of:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagMap1296
```

After that selector source exists, a separate structural tag-map/separation
burden will still remain: a `Fin 1296` code on residual values, not on the
selected image.

## Why existing routes do not close the target

`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296`
has the shape of a selector theorem, but using it here would import the
selected-image-cardinality route.  The current task explicitly forbids using
selected-image cardinality or `finsetCodeOfCardLe` on an already bounded
selected image to manufacture the tag map.

The `terminalNeighborCode` field in
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` is
parent-relative local selector evidence.  Equality of those fields is not an
ambient residual-value tag and does not prove equality of selected
terminal-neighbor values across distinct essential parents.

Likewise, local displacement/neighbor codes, residual size, raw frontier,
residual paths, root-shell reachability, deleted-vertex adjacency, and empirical
search do not provide the required residual-subtype tag-map injectivity.

## Rejected routes

This attempt did not use:

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

`lake build YangMills.ClayCore.LatticeAnimalCount` passed.

No new theorem was introduced in this attempt, so no new theorem-specific
`#print axioms` trace is required.  The v2.179 bridge remains at
`[propext, Classical.choice, Quot.sound]`.

F3-COUNT remains `CONDITIONAL_BRIDGE`; no percentage, status, README metric,
planner metric, ledger row, or Clay-level claim moved.

## Next Codex task

`CODEX-F3-RESIDUAL-FIBER-TERMINAL-NEIGHBOR-SELECTOR-SOURCE-SCOPE-001`

Scope the missing non-circular residual-local terminal-neighbor selector source
needed before the residual bookkeeping tag map can be proved.
