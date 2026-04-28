# F3 residual-fiber terminal-neighbor selector source interface v2.182

Task: `CODEX-F3-RESIDUAL-FIBER-TERMINAL-NEIGHBOR-SELECTOR-SOURCE-INTERFACE-001`

Status: `DONE_INTERFACE_AND_BRIDGE_LANDED_NO_STATUS_MOVE`

## Lean landing

Added the no-sorry selector-only interface:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296
```

Location:

```text
YangMills/ClayCore/LatticeAnimalCount.lean:3913
```

The interface uses the v2.121 bookkeeping residual-fiber hypotheses and exposes
only:

- `terminalNeighborOfParent`;
- `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`.

It does not expose a residual-value tag map, selected-value separation, or a
selected-image cardinality bound.

## Compatible downstream tag-code premise

Added the separate compatible tag-code premise:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagCodeForSelector1296
```

Location:

```text
YangMills/ClayCore/LatticeAnimalCount.lean:3974
```

This second interface is intentionally not part of the selector source.  It is
parameterized by a fixed `terminalNeighborOfParent` and its selector evidence,
then supplies the residual-subtype `bookkeepingTagCode` and selected-value
separation needed by the full tag-map interface.

## Bridge landed

Added the no-sorry two-premise packaging bridge:

```lean
physicalPlaquetteGraphResidualFiberBookkeepingTagMap1296_of_residualFiberTerminalNeighborSelectorSource1296_of_residualFiberBookkeepingTagCodeForSelector1296
```

Location:

```text
YangMills/ClayCore/LatticeAnimalCount.lean:4111
```

Bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagMap1296
```

The bridge only:

1. obtains `terminalNeighborOfParent` and selector evidence from
   `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296`;
2. applies `PhysicalPlaquetteGraphResidualFiberBookkeepingTagCodeForSelector1296`
   to that exact selector and evidence;
3. packages the four fields required by
   `PhysicalPlaquetteGraphResidualFiberBookkeepingTagMap1296`.

## Explicit non-routes

This interface and bridge do not use:

- selected-image cardinality;
- `finsetCodeOfCardLe` on an already bounded selected image;
- the v2.161 cycle
  `SelectorImageBound → SelectorCodeSeparation → CodeSeparation →
   DominatingMenu → ImageCompression → SelectorImageBound`;
- local displacement codes;
- parent-relative `terminalNeighborCode` equality;
- residual size or raw frontier;
- residual paths alone;
- root-shell reachability alone;
- local degree;
- deleted-vertex adjacency;
- empirical bounded search;
- post-hoc terminal-neighbor choices from a current witness.

## Validation

Command:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result: passed.

The new bridge axiom trace is:

```text
YangMills.physicalPlaquetteGraphResidualFiberBookkeepingTagMap1296_of_residualFiberTerminalNeighborSelectorSource1296_of_residualFiberBookkeepingTagCodeForSelector1296:
  [propext, Classical.choice, Quot.sound]
```

F3-COUNT remains `CONDITIONAL_BRIDGE`; no percentage, status, README metric,
planner metric, ledger row, or Clay-level claim moved.

## Next Codex task

```text
CODEX-F3-PROVE-RESIDUAL-FIBER-TERMINAL-NEIGHBOR-SELECTOR-SOURCE-001
```

Prove `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296`
or reduce it to the next exact no-closure blocker.
