# F3 residual-fiber terminal-neighbor selector source proof attempt v2.183

Task: `CODEX-F3-PROVE-RESIDUAL-FIBER-TERMINAL-NEIGHBOR-SELECTOR-SOURCE-001`

Status: `DONE_REDUCED_TO_TERMINAL_NEIGHBOR_DOMINATION_NO_STATUS_MOVE`

## Attempted target

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296
```

The target was not proved directly from the v2.121 bookkeeping residual-fiber
hypotheses alone.  Those hypotheses supply `deleted`, `parentOf`, `essential`,
the essential image identity, and essential-subset-residual facts, but they do
not construct a residual-local terminal-neighbor selector.

## Lean reduction landed

Added the no-sorry reduction:

```lean
physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296_of_residualFiberTerminalNeighborDominatingMenu1296
```

Location:

```text
YangMills/ClayCore/LatticeAnimalCount.lean:4877
```

Source premise:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominatingMenu1296
```

Target:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296
```

The proof projects, for each residual fiber and essential parent, the dominated
terminal neighbor supplied by the existing dominating-menu relation.  It then
uses the `Nonempty PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`
witness from that relation as the required selector evidence.

## Sharpened blocker

The exact no-closure blocker is not selected-image cardinality.  The new
reduction shows that selector-source construction is supplied by the domination
relation part of:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominatingMenu1296
```

More sharply, the proof ignores the menu-cardinality field.  A future upstream
theorem could isolate just a residual-local terminal-neighbor domination relation
that provides:

- a residual terminal-neighbor candidate for every essential parent;
- membership of that candidate in the residual;
- `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` for that
  selected candidate.

Such a theorem would be sufficient for the selector source without proving a
bounded selected image or a bounded menu.

## Explicit non-routes

The reduction does not use:

- selected-image cardinality;
- `finsetCodeOfCardLe` on an already bounded selected image;
- the v2.161 cycle
  `SelectorImageBound -> SelectorCodeSeparation -> CodeSeparation ->
   DominatingMenu -> ImageCompression -> SelectorImageBound`;
- local displacement codes;
- parent-relative `terminalNeighborCode` equality;
- local degree;
- residual paths alone;
- root-shell reachability alone;
- residual size;
- raw frontier;
- deleted-vertex adjacency;
- empirical bounded search;
- post-hoc terminal-neighbor choices from a current witness.

## Validation

Command:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result: passed.

The new theorem axiom trace is:

```text
YangMills.physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296_of_residualFiberTerminalNeighborDominatingMenu1296:
  [propext, Classical.choice, Quot.sound]
```

F3-COUNT remains `CONDITIONAL_BRIDGE`; no percentage, status, README metric,
planner metric, ledger row, or Clay-level claim moved.

## Next Codex task

```text
CODEX-F3-TERMINAL-NEIGHBOR-DOMINATION-RELATION-SCOPE-001
```
