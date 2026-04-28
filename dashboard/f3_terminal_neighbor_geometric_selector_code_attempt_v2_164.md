# F3 residual terminal-neighbor geometric selector-code proof attempt v2.164

Task: `CODEX-F3-PROVE-TERMINAL-NEIGHBOR-GEOMETRIC-SELECTOR-CODE-001`

## Attempted Target

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborGeometricSelectorCode1296
```

## Result

No proof was added.

The existing Lean ingredients do not construct the required residual-local
`Fin 1296` geometric selector code with pairwise selected-value separation
across essential parents in a residual fiber.

## What Existing Data Gives

The current file contains local geometric coding tools such as:

- `siteNeighborTernaryCode`;
- `siteNeighborTernaryCode_injective`;
- `plaquetteNeighborStepCodeOfChoice`;
- `plaquetteNeighborStepCodeOfChoice_injOn`;
- `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParentCode1296`;
- the per-witness `terminalNeighborCode` field inside
  `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`.

These are not enough for the target theorem.

The local codes separate neighbors relative to a fixed base point.  The target
requires a code whose equality across two possibly different essential parents
in the same residual fiber forces equality of the selected terminal-neighbor
values themselves:

```lean
terminalNeighborGeometricCode residual p =
    terminalNeighborGeometricCode residual q →
  (terminalNeighborOfParent residual p).1 =
    (terminalNeighborOfParent residual q).1
```

A per-parent local displacement code cannot prove this, because equal
displacements from different parent/base vertices need not identify the same
absolute terminal-neighbor plaquette.

## Exact No-Closure Blocker

The missing theorem is a residual-local, basepoint-independent terminal-neighbor
geometric code/separation principle.

Tentative next target:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborBasepointIndependentCode1296
```

It should construct:

- residual-local `terminalNeighborOfParent`;
- `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`;
- a `Fin 1296` code for the selected terminal-neighbor value that is not merely
  a local displacement code from the current parent;
- pairwise selected-value separation across all essential parents in the same
  residual fiber.

## Rejected Routes

This attempt explicitly rejects:

- using `finsetCodeOfCardLe` on the already bounded selected image;
- routing through the v2.161 cycle:

```text
SelectorImageBound -> SelectorCodeSeparation -> CodeSeparation
  -> DominatingMenu -> ImageCompression -> SelectorImageBound
```

- treating the existence of `terminalNeighborCode` as injectivity;
- local degree or local neighbor existence;
- residual path existence or splitting;
- root or root-shell reachability;
- residual size or raw residual frontier;
- deleted-vertex adjacency outside the residual;
- empirical bounded search;
- packing or projection of an already bounded menu;
- post-hoc terminal neighbors chosen from a current `(X, deleted X)` witness.

## Validation

No Lean theorem was added by this attempt.  The existing v2.163 bridge remains
the latest Lean change in this area.

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

passed.

The relevant existing v2.163 bridge trace remains:

```text
[propext, Classical.choice, Quot.sound]
```

F3-COUNT remains `CONDITIONAL_BRIDGE`.  No status, percentage, README metric,
planner metric, ledger row, or Clay-level claim moved.
