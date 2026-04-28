# F3 residual terminal-neighbor image compression interface (v2.151)

Task: `CODEX-F3-TERMINAL-NEIGHBOR-IMAGE-COMPRESSION-INTERFACE-001`

## Result

Added the no-sorry Lean interface:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborImageCompression1296
```

and proved the projection bridge:

```lean
physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296_of_residualFiberTerminalNeighborImageCompression1296
```

Bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296
```

## Lean Locations

```text
YangMills/ClayCore/LatticeAnimalCount.lean:3872
  def PhysicalPlaquetteGraphResidualFiberTerminalNeighborImageCompression1296

YangMills/ClayCore/LatticeAnimalCount.lean:4045
  theorem physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296_of_residualFiberTerminalNeighborImageCompression1296

YangMills/ClayCore/LatticeAnimalCount.lean:6962
  #print axioms physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296_of_residualFiberTerminalNeighborImageCompression1296
```

## Interface Shape

The compression interface exposes:

* a residual-indexed `terminalNeighborMenu`;
* `terminalNeighborMenu residual ⊆ residual`;
* `(terminalNeighborMenu residual).card ≤ 1296`;
* a residual-indexed `terminalNeighborOfParent` selector;
* selector membership in the bounded menu;
* residual-local
  `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`;
* selected image cover
  `((essential residual).attach.image ... ) ⊆ terminalNeighborMenu residual`.

The bridge is projection-only. It reuses the selector and selector evidence, then
derives selected-image cardinality by `Finset.card_le_card` applied to the image
cover and the menu-cardinality bound.

## Non-Substitutes

The interface does not derive selected-image cardinality from local neighbor
existence, residual path existence/splitting, root/root-shell reachability,
local degree of one fixed plaquette, residual size, raw frontier growth,
deleted-vertex adjacency outside the residual, empirical search, or packing of
an already bounded menu.

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

Attempt the compression producer:

```text
CODEX-F3-PROVE-TERMINAL-NEIGHBOR-IMAGE-COMPRESSION-001
```
