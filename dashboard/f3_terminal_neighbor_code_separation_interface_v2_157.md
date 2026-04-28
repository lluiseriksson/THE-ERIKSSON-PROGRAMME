# F3 residual terminal-neighbor code-separation interface (v2.157)

Task: `CODEX-F3-TERMINAL-NEIGHBOR-CODE-SEPARATION-INTERFACE-001`

## Result

Added the no-sorry Lean interface:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborCodeSeparation1296
```

and the projection bridge:

```lean
physicalPlaquetteGraphResidualFiberTerminalNeighborDominatingMenu1296_of_residualFiberTerminalNeighborCodeSeparation1296
```

Bridge conclusion:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominatingMenu1296
```

The bridge builds the dominating menu as the selected terminal-neighbor image.

## Interface Shape

The new interface quantifies over the same v2.121 bookkeeping data used by the
terminal-neighbor route: `root`, `k`, `deleted`, `parentOf`, `essential`, the
safe-deletion choice, the essential image identity, and the essential subset
residual hypothesis.

It then exposes:

* a residual-indexed selector `terminalNeighborOfParent`;
* residual-local `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`
  for each selected neighbor;
* a `Fin 1296` code on the selected terminal-neighbor image;
* injectivity of that code;
* the selected-image cardinality bound `<= 1296`.

The cardinality bound is therefore tied to explicit selected-image code
separation, not to a local-degree or path-existence surrogate.

## Bridge

The bridge takes:

```lean
hseparation :
  PhysicalPlaquetteGraphResidualFiberTerminalNeighborCodeSeparation1296
```

and proves:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominatingMenu1296
```

by defining:

```lean
terminalNeighborMenu residual :=
  (essential residual).attach.image
    (fun p => (terminalNeighborOfParent residual p).1)
```

The menu subset proof unpacks `Finset.mem_image` and uses the residual
membership carried by `terminalNeighborOfParent`.  The menu cardinality is the
selected-image bound supplied by the code-separation interface.  Domination is
obtained by choosing the selector value for each essential parent and wrapping
the corresponding selector data in `Nonempty`.

No terminal neighbor is chosen post-hoc from a current `(X, deleted X)` witness.

## Non-Substitutes

This interface and bridge do not treat any of the following as selected-image
code separation:

* local degree of one fixed plaquette;
* residual path existence or splitting;
* root or root-shell reachability;
* residual size or raw residual frontier;
* deleted-vertex adjacency outside the residual;
* empirical search;
* packing or projection of an already bounded menu.

## Validation

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

passed.

The new bridge axiom trace is:

```text
[propext, Classical.choice, Quot.sound]
```

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No status, percentage, README metric,
planner metric, ledger row, or Clay-level claim moved.

## Next Task

Prove or precisely fail the new code-separation theorem:

```text
CODEX-F3-PROVE-TERMINAL-NEIGHBOR-CODE-SEPARATION-001
```
