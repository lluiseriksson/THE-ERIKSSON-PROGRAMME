# F3 residual canonical terminal-neighbor image interface (v2.145)

Task: `CODEX-F3-TERMINAL-NEIGHBOR-IMAGE-BOUND-INTERFACE-001`

## Result

Added the no-sorry Lean structure:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalTerminalNeighborData
```

Added the no-sorry Lean Prop/interface:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalTerminalNeighborImageBound1296
```

and proved the projection bridge:

```lean
physicalPlaquetteGraphResidualFiberCanonicalTerminalSuffixImageBound1296_of_residualFiberCanonicalTerminalNeighborImageBound1296
```

with target:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalTerminalSuffixImageBound1296
```

## Lean locations

```text
YangMills/ClayCore/LatticeAnimalCount.lean:3359
YangMills/ClayCore/LatticeAnimalCount.lean:3771
YangMills/ClayCore/LatticeAnimalCount.lean:3825
YangMills/ClayCore/LatticeAnimalCount.lean:6717
```

## Interface separation

The new terminal-neighbor data names the selected residual-local terminal
neighbor directly:

- `terminalNeighbor` is a plaquette inside the residual;
- `prefixToTerminalNeighbor` records residual-local prefix evidence to that
  selected neighbor;
- `terminalNeighborSuffix` records residual-local suffix evidence from the
  selected neighbor to the essential parent target;
- `terminalNeighbor_is_last_edge` carries final-edge adjacency inside the
  residual for non-singleton residual fibers;
- `terminalNeighborCode : Fin 1296` records the code for the selected terminal
  neighbor.

The Prop keeps the load-bearing selected terminal-neighbor image-cardinality
bound explicit:

```lean
((essential residual).attach.image
  (fun p => (terminalNeighborData residual p).terminalNeighbor.1)).card ≤ 1296
```

The bridge is projection-only: it renames `terminalNeighbor` as the terminal
predecessor field of `PhysicalPlaquetteGraphResidualFiberCanonicalTerminalSuffixData`
and carries the selected-image bound unchanged.

## Non-confusions

The interface does not assert that residual path existence or path splitting
proves the selected-image bound.

It does not use root/root-shell reachability, local degree, residual size, raw
frontier growth, deleted-vertex adjacency outside the residual, empirical
bounded search, or packing an already bounded menu as a substitute for the
selected terminal-neighbor image-cardinality bound.

It also does not prove the producer theorem. The remaining mathematical target
is to construct the residual-local terminal-neighbor data and selected-image
bound over the v2.121 bookkeeping residual fibers.

## Validation

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

passed.

The new bridge theorem-specific axiom trace is:

```text
[propext, Classical.choice, Quot.sound]
```

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No status, percentage, README metric,
planner metric, or Clay-level claim moved.

## Next task

Prove or precisely fail:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalTerminalNeighborImageBound1296
```

The proof must construct the residual-local selected terminal-neighbor data and
the selected image-cardinality bound honestly, without replacing the bound by
path existence, root-shell reachability, local degree, residual size, raw
frontier growth, packing, or deleted-vertex adjacency outside the residual.
