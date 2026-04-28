# F3 residual terminal-neighbor geometric selector-code interface v2.163

Task: `CODEX-F3-TERMINAL-NEIGHBOR-GEOMETRIC-SELECTOR-CODE-INTERFACE-RETRY-001`

## Result

Codex added the no-sorry Lean Prop/interface:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborGeometricSelectorCode1296
```

and the no-sorry projection bridge:

```lean
physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296_of_residualFiberTerminalNeighborGeometricSelectorCode1296
```

Bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296
```

Lean locations:

- `YangMills/ClayCore/LatticeAnimalCount.lean:3876` defines the interface.
- `YangMills/ClayCore/LatticeAnimalCount.lean:3944` proves the bridge.
- `YangMills/ClayCore/LatticeAnimalCount.lean:7531` prints the bridge axioms.

## Interface Shape

The interface exposes, over the v2.121 residual-fiber bookkeeping data:

- residual-local `terminalNeighborOfParent`;
- `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` for each essential parent;
- an independent `Fin 1296` geometric selector code;
- pairwise selected-value separation: equal geometric codes force equal selected terminal-neighbor values.

This is deliberately independent of the v2.161 circular route:

```text
SelectorImageBound -> SelectorCodeSeparation -> CodeSeparation
  -> DominatingMenu -> ImageCompression -> SelectorImageBound
```

## Bridge Mechanics

For each residual fiber, the bridge forms the selected terminal-neighbor image and codes each selected value by choosing an essential-parent witness of image membership. Pairwise selected-value separation makes this induced selected-image code injective into `Fin 1296`, and the cardinality bound follows from `Fintype.card_le_of_injective`.

The bridge does not use `finsetCodeOfCardLe` on an already bounded selected image.

## Rejected Routes

This interface and bridge do not derive the selected-image cardinality bound from:

- selector-code separation, code separation, dominating menus, or image compression;
- local degree;
- residual path existence or splitting;
- root or root-shell reachability;
- residual size or raw residual frontier;
- deleted-vertex adjacency outside the residual;
- empirical bounded search;
- packing or projection of an already bounded menu;
- post-hoc terminal neighbors chosen from a current `(X, deleted X)` witness.

## Validation

`lake build YangMills.ClayCore.LatticeAnimalCount` passed after the Lean edit.

The new bridge axiom trace is:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, new project axiom, empirical evidence, status move, percentage move, README metric move, planner metric move, ledger row move, or Clay-level claim was introduced.

F3-COUNT remains `CONDITIONAL_BRIDGE`.

## Next Blocker

The remaining no-closure blocker is the source theorem itself:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborGeometricSelectorCode1296
```

Next task should prove it or reduce it to the next exact blocker by constructing residual-local selector data and an independent `Fin 1296` geometric selector code with pairwise selected-value separation.
