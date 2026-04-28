# F3 residual terminal-neighbor selector-code separation interface (v2.160)

Task: `CODEX-F3-TERMINAL-NEIGHBOR-SELECTOR-CODE-SEPARATION-INTERFACE-001`

## Result

Added the no-sorry Lean interface:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorCodeSeparation1296
```

and proved the projection bridge:

```lean
physicalPlaquetteGraphResidualFiberTerminalNeighborCodeSeparation1296_of_residualFiberTerminalNeighborSelectorCodeSeparation1296
```

Bridge conclusion:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborCodeSeparation1296
```

## Interface Shape

The interface quantifies over the same v2.121 bookkeeping inputs as the v2.157
selected-image code-separation interface: `root`, `k`, `deleted`, `parentOf`,
`essential`, the safe-deletion choice, the essential image identity, and the
essential subset residual hypothesis.

It exposes:

* a residual-indexed `terminalNeighborOfParent` selector;
* residual-local `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`;
* a pairwise selector-code separation clause:

```lean
∀ residual
  (p q : {p : ConcretePlaquette physicalClayDimension L //
    p ∈ essential residual}),
  (terminalNeighborSelectorEvidence residual p).terminalNeighborCode =
      (terminalNeighborSelectorEvidence residual q).terminalNeighborCode →
    (terminalNeighborOfParent residual p).1 =
      (terminalNeighborOfParent residual q).1
```

* the selected terminal-neighbor image card bound `<= 1296`.

The card bound is carried explicitly so the projection bridge is a stable
Lean repackaging theorem rather than a hidden finite-cardinality proof.

## Bridge

The bridge defines the v2.157 selected-image code by choosing, for each image
element, a parent witness from `Finset.mem_image` and reading that witness's
`terminalNeighborCode`.

Injectivity is proved by:

1. unpacking the two chosen parent witnesses;
2. applying the selector-code separation clause to equal image codes;
3. using the image-witness equalities to identify the selected terminal-neighbor
   values.

No terminal neighbor is chosen post-hoc from a current `(X, deleted X)` witness.

## Non-Substitutes

This interface and bridge do not treat any of the following as selected-image
separation:

* the mere existence of a per-witness `terminalNeighborCode`;
* local degree of one fixed plaquette;
* residual path existence or path splitting;
* root or root-shell reachability;
* residual size or raw residual frontier;
* deleted-vertex adjacency outside the residual;
* empirical bounded search;
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

While landing this bridge, the existing v2.157 bridge
`physicalPlaquetteGraphResidualFiberTerminalNeighborDominatingMenu1296_of_residualFiberTerminalNeighborCodeSeparation1296`
was made explicit at its selected-image witness and now also prints the same
clean axiom trace.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No status, percentage, README metric,
planner metric, ledger row, or Clay-level claim moved.

## Next Task

Prove or precisely fail the selector-code separation theorem:

```text
CODEX-F3-PROVE-TERMINAL-NEIGHBOR-SELECTOR-CODE-SEPARATION-001
```
