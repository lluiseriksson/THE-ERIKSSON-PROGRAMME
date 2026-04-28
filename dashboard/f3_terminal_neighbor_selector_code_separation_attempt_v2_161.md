# F3 residual terminal-neighbor selector-code separation proof attempt (v2.161)

Task: `CODEX-F3-PROVE-TERMINAL-NEIGHBOR-SELECTOR-CODE-SEPARATION-001`

## Result

Attempted to prove:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorCodeSeparation1296
```

No unconditional proof of the proposition was added.  Instead, Codex proved the
no-sorry reduction bridge:

```lean
physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorCodeSeparation1296_of_residualFiberTerminalNeighborSelectorImageBound1296
```

Bridge premise:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296
```

Bridge conclusion:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorCodeSeparation1296
```

## What Closed

The pairwise selector-code separation burden is no longer a separate Lean
bookkeeping blocker once a selected-image bound is available.

The reduction reuses the residual-local selector and
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` supplied by
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296`.
It then replaces only the per-witness `terminalNeighborCode` field with the
canonical code:

```lean
finsetCodeOfCardLe selectedImage hcard
```

Pairwise code separation follows from:

```lean
finsetCodeOfCardLe_injective selectedImage hcard
```

This is a structural repackaging of an already bounded selected image, not a
proof of the selected-image cardinality bound itself.

## Exact No-Closure Blocker

The remaining blocker is an independent, non-circular proof of:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296
```

The existing chain cannot be used to close it without circularity:

```text
SelectorImageBound
  -> SelectorCodeSeparation      (v2.161 bridge)
  -> CodeSeparation              (v2.160 bridge)
  -> DominatingMenu              (v2.157 bridge)
  -> ImageCompression            (v2.154 bridge)
  -> SelectorImageBound          (v2.151 bridge)
```

Therefore the next target must produce the selector-image bound independently
from residual-local construction data, not by cycling through the v2.161 bridge.

## Non-Substitutes

The blocker is not discharged by:

* treating the original per-witness `terminalNeighborCode` as injective;
* local degree of one fixed plaquette;
* residual path existence or path splitting;
* root or root-shell reachability;
* residual size or raw residual frontier;
* deleted-vertex adjacency outside the residual;
* empirical bounded search;
* packing or projection of an already bounded menu;
* the circular chain from selector-image bound back to itself.

## Validation

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

passed.

The new reduction bridge axiom trace is:

```text
[propext, Classical.choice, Quot.sound]
```

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No status, percentage, README metric,
planner metric, ledger row, or Clay-level claim moved.

## Next Task

Scope the independent, non-circular selector-image bound route:

```text
CODEX-F3-TERMINAL-NEIGHBOR-SELECTOR-IMAGE-INDEPENDENCE-SCOPE-001
```
