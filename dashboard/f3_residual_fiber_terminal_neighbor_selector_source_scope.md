# F3 residual-fiber terminal-neighbor selector source scope v2.181

Task: `CODEX-F3-RESIDUAL-FIBER-TERMINAL-NEIGHBOR-SELECTOR-SOURCE-SCOPE-001`

Status: `DONE_SCOPE_DELIVERED_NO_LEAN_NO_STATUS_MOVE`

## Proposed Lean source theorem

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296
```

This theorem should sit strictly upstream of:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagMap1296
```

Its job is only to construct the residual-local terminal-neighbor selector
payload:

```lean
∃ terminalNeighborOfParent :
  ∀ residual,
    (p : {p : ConcretePlaquette physicalClayDimension L //
      p ∈ essential residual}) →
      {q : ConcretePlaquette physicalClayDimension L // q ∈ residual},
∃ terminalNeighborSelectorEvidence :
  ∀ residual,
    (p : {p : ConcretePlaquette physicalClayDimension L //
      p ∈ essential residual}) →
      PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
        residual p.1 (terminalNeighborOfParent residual p),
  True
```

The source theorem should use the same v2.121 bookkeeping hypotheses as the
tag-map interface:

- the total `deleted`, `parentOf`, and `essential` functions;
- the safe-deletion/parent choice clause;
- the residual-fiber image identity for `essential`;
- the proof that `essential residual ⊆ residual`.

It must not include a residual-value `Fin 1296` tag map and must not state
selected-value injectivity. Those are separate downstream burdens.

## Exact bridge into the tag-map target

The selector source alone is not enough to prove the full tag-map target,
because `PhysicalPlaquetteGraphResidualFiberBookkeepingTagMap1296` also needs a
residual-subtype bookkeeping tag map and selected-value separation.  The exact
bridge should therefore be a two-premise packaging bridge:

```lean
physicalPlaquetteGraphResidualFiberBookkeepingTagMap1296_of_residualFiberTerminalNeighborSelectorSource1296_of_residualFiberBookkeepingTagCodeForSelector1296
```

with target:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagMap1296
```

The intended premises are:

```lean
hselector :
  PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296

htagForSelector :
  PhysicalPlaquetteGraphResidualFiberBookkeepingTagCodeForSelector1296
```

where the second premise is a later theorem scoped around a fixed
`terminalNeighborOfParent` and its
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`, supplying:

```lean
∃ bookkeepingTagCode :
  ∀ residual,
    {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} →
      Fin 1296,
  ∀ residual
    (p q : {p : ConcretePlaquette physicalClayDimension L //
      p ∈ essential residual}),
    bookkeepingTagCode residual (terminalNeighborOfParent residual p) =
      bookkeepingTagCode residual (terminalNeighborOfParent residual q) →
      (terminalNeighborOfParent residual p).1 =
        (terminalNeighborOfParent residual q).1
```

The bridge should only combine the two payloads:

1. obtain `terminalNeighborOfParent` and selector evidence from `hselector`;
2. apply `htagForSelector` to that exact selector and evidence;
3. package selector, evidence, `bookkeepingTagCode`, and selected-value
   separation as `PhysicalPlaquetteGraphResidualFiberBookkeepingTagMap1296`.

## Why this is the right next split

The v2.180 no-closure attempt showed that v2.121 bookkeeping does not construct
`terminalNeighborOfParent` or
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`.  It only
supplies `deleted`, `parentOf`, `essential`, residual image, and subset
bookkeeping.  Thus the selector source is the first missing object before any
bookkeeping tag map can be applied.

This split also prevents a circular proof shape.  If the selector source were
derived from `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296`,
then the proof would import selected-image cardinality and could route back
through the v2.161 cycle.  That is not allowed here.

## Explicit non-routes

This scope does not use or propose:

- selected-image cardinality;
- `finsetCodeOfCardLe` on an already bounded selected image;
- the v2.161 cycle
  `SelectorImageBound → SelectorCodeSeparation → CodeSeparation →
   DominatingMenu → ImageCompression → SelectorImageBound`;
- local displacement codes;
- parent-relative `terminalNeighborCode` equality;
- residual size or raw frontier bounds;
- residual paths alone;
- root-shell reachability alone;
- local degree;
- deleted-vertex adjacency;
- empirical bounded search;
- post-hoc terminal-neighbor choices from a current `(X, deleted X)` witness.

## Validation

Dashboard-only scope.  No Lean file was edited and no lake build is required.

F3-COUNT remains `CONDITIONAL_BRIDGE`; no percentage, status, README metric,
planner metric, ledger row, or Clay-level claim moved.

## Next Codex task

```text
CODEX-F3-RESIDUAL-FIBER-TERMINAL-NEIGHBOR-SELECTOR-SOURCE-INTERFACE-001
```

Add the no-sorry Lean Prop/interface
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296` and,
only if it builds without sorry, add the two-premise bridge skeleton into
`PhysicalPlaquetteGraphResidualFiberBookkeepingTagMap1296` once the compatible
tag-code-for-selector premise is explicitly represented.
