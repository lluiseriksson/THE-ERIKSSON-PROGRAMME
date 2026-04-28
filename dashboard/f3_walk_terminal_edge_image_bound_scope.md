# F3 walk terminal-edge selected-image bound scope (v2.138)

Task: `CODEX-F3-WALK-TERMINAL-EDGE-IMAGE-BOUND-SCOPE-001`

## Result

Scoped the next Lean-stable target behind the v2.137 blocker:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalWalkTerminalEdgeImageBound1296
```

The intended bridge is:

```lean
physicalPlaquetteGraphResidualFiberCanonicalTerminalEdgeSelector1296_of_residualFiberCanonicalWalkTerminalEdgeImageBound1296
```

with target:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalTerminalEdgeSelector1296
```

No Lean file was edited in this scope pass.

## Proposed contract

The new proposition should quantify over the same v2.121 bookkeeping fibers used by
`PhysicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296`: `root`, `k`,
`deleted`, `parentOf`, `essential`, the safe/low-cardinality choice evidence, the
fiber identity, and `essential ⊆ residual`.

For each residual fiber and essential parent, it should expose residual-only data:

- a canonical residual walk or path-code datum from residual information, not from
  the current `(X, deleted X)` witness;
- an extracted immediate terminal predecessor lying in the residual;
- last-edge adjacency between that predecessor and the essential parent whenever
  the residual fiber is non-singleton;
- residual path/walk evidence connecting the predecessor data to the selected
  parent;
- an explicit selected-image bound, preferably as an injective code into
  `Fin 1296` for the image of the selected terminal predecessors over the fiber.

The bridge should repack this data into
`PhysicalPlaquetteGraphResidualFiberCanonicalTerminalEdgeData`, then into
`PhysicalPlaquetteGraphResidualFiberCanonicalTerminalEdgeSelector1296`.

## What this is not

This target is not implied by plain residual path existence. A path proves a
connection exists, but does not bound the image of the immediate terminal
predecessors selected across the whole residual fiber.

It is also not a root/root-shell reachability theorem. First-shell or root-shell
parents may reach an essential parent without being the terminal predecessor
adjacent to that parent.

It is not a local-degree bound for one fixed plaquette, a residual-size bound, or
a raw residual-frontier bound. The bound must be on the selected terminal
predecessor image over the fiber.

It is not merely the v2.124 packing theorem. Packing can encode an already
bounded explicit menu; it does not construct the residual-local selected menu or
prove its image cardinality.

Finally, deleted-vertex adjacency outside the residual cannot be used as terminal
predecessor data.

## Validation

Dashboard-only scope artifact created. No Lean file was edited, so
`lake build YangMills.ClayCore.LatticeAnimalCount` was not required for this
scope step. The previous v2.137 attempt already recorded a passing build for the
current Lean state.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`; no status, percentage, README metric,
planner metric, or Clay-level claim moved.

## Next task

Create the no-sorry Lean interface and safe bridge if possible:

```text
CODEX-F3-WALK-TERMINAL-EDGE-IMAGE-BOUND-INTERFACE-001
```
