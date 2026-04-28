# F3 residual terminal-neighbor selector image interface (v2.148)

Task: `CODEX-F3-TERMINAL-NEIGHBOR-SELECTOR-IMAGE-INTERFACE-001`

## Result

Added the no-sorry Lean selector interface:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296
```

and proved the projection bridge:

```lean
physicalPlaquetteGraphResidualFiberCanonicalTerminalNeighborImageBound1296_of_residualFiberTerminalNeighborSelectorImageBound1296
```

The bridge target is:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalTerminalNeighborImageBound1296
```

## Lean Locations

```text
YangMills/ClayCore/LatticeAnimalCount.lean:3364
  structure PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData

YangMills/ClayCore/LatticeAnimalCount.lean:3808
  def PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296

YangMills/ClayCore/LatticeAnimalCount.lean:3926
  theorem physicalPlaquetteGraphResidualFiberCanonicalTerminalNeighborImageBound1296_of_residualFiberTerminalNeighborSelectorImageBound1296

YangMills/ClayCore/LatticeAnimalCount.lean:6861
  #print axioms physicalPlaquetteGraphResidualFiberCanonicalTerminalNeighborImageBound1296_of_residualFiberTerminalNeighborSelectorImageBound1296
```

## Interface Shape

The interface exposes:

* a residual-indexed selector `terminalNeighborOfParent`;
* selector evidence
  `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` tied to the
  selected terminal neighbor;
* final-edge adjacency inside the residual for the selected terminal neighbor;
* residual-local canonical walk/prefix/suffix evidence;
* selected terminal-neighbor image cardinality `<= 1296`.

The bridge is projection-only. It copies the selected
`terminalNeighborOfParent` into
`PhysicalPlaquetteGraphResidualFiberCanonicalTerminalNeighborData` and carries
the selected-image bound unchanged.

## Non-Substitutes

The interface does not treat residual path existence/splitting,
root/root-shell reachability, local degree of one fixed plaquette, residual
size, raw frontier growth, deleted-vertex adjacency outside the residual, or
packing of an already bounded menu as proof of selected-image cardinality.

It does not choose terminal neighbors post-hoc from a current `(X, deleted X)`
witness.

## Validation

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

passed.

The new bridge theorem has axiom trace:

```text
[propext, Classical.choice, Quot.sound]
```

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No status, percentage, README metric,
planner metric, or Clay-level claim moved.

## Next Task

Attempt the producer:

```text
CODEX-F3-PROVE-TERMINAL-NEIGHBOR-SELECTOR-IMAGE-BOUND-001
```

