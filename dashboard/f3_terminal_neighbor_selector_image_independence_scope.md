# F3 residual terminal-neighbor selector-image independence scope (v2.162)

Task: `CODEX-F3-TERMINAL-NEIGHBOR-SELECTOR-IMAGE-INDEPENDENCE-SCOPE-001`

## Result

Scoped the next non-circular route to:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296
```

The exact bridge target remains the v2.148 selector-image interface:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296
```

The proposed independent source theorem is:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborGeometricSelectorCode1296
```

with intended bridge:

```lean
physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296_of_residualFiberTerminalNeighborGeometricSelectorCode1296
```

## Why This Is Needed

v2.161 proved only a reduction:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296
  -> PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorCodeSeparation1296
```

using `finsetCodeOfCardLe` on the already bounded selected image.  Therefore
the chain

```text
SelectorImageBound
  -> SelectorCodeSeparation
  -> CodeSeparation
  -> DominatingMenu
  -> ImageCompression
  -> SelectorImageBound
```

is circular and cannot close `SelectorImageBound`.

The new route must produce a selector and a separating `Fin 1296` code before
the selected-image bound is known.

## Proposed Interface Shape

The new theorem should quantify over the same v2.121 bookkeeping data as
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296`:

* `root`, `k`;
* `deleted`, `parentOf`;
* `essential`;
* the safe-deletion choice hypothesis;
* the essential image identity;
* the essential-subset residual hypothesis.

It should then construct:

```lean
terminalNeighborOfParent :
  ∀ residual,
    (p : {p : ConcretePlaquette physicalClayDimension L //
      p ∈ essential residual}) →
      {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}
```

plus residual-local evidence:

```lean
terminalNeighborSelectorEvidence :
  ∀ residual,
    (p : {p : ConcretePlaquette physicalClayDimension L //
      p ∈ essential residual}) →
      PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
        residual p.1 (terminalNeighborOfParent residual p)
```

and, crucially, an independent geometric code:

```lean
terminalNeighborGeometricCode :
  ∀ residual,
    (p : {p : ConcretePlaquette physicalClayDimension L //
      p ∈ essential residual}) → Fin 1296
```

with pairwise selected-value separation:

```lean
∀ residual
  (p q : {p : ConcretePlaquette physicalClayDimension L //
    p ∈ essential residual}),
  terminalNeighborGeometricCode residual p =
      terminalNeighborGeometricCode residual q →
    (terminalNeighborOfParent residual p).1 =
      (terminalNeighborOfParent residual q).1
```

The code must be produced from residual-local canonical terminal-neighbor
construction data, not from `finsetCodeOfCardLe` applied to the selected image,
not from a bounded menu, and not from post-hoc current deletion witnesses.

## Narrow Finite-Card Bridge

The bridge to `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296`
is then a finite-cardinality projection:

1. reuse `terminalNeighborOfParent`;
2. reuse `terminalNeighborSelectorEvidence`;
3. define a code on each selected-image element by choosing an essential-parent
   witness from `Finset.mem_image`;
4. prove this image code is well-defined/injective using the pairwise separation
   theorem above;
5. obtain selected-image card `<= 1296` from injection into `Fin 1296`.

This bridge is allowed to use `Classical.choice` for image witnesses.  It is not
allowed to use `finsetCodeOfCardLe selectedImage hcard`, because that would
already assume the desired selected-image cardinality.

## Non-Substitutes

This scope explicitly rejects:

* the v2.161 circular route through `SelectorCodeSeparation`, `CodeSeparation`,
  `DominatingMenu`, and `ImageCompression`;
* local degree of one fixed plaquette;
* residual path existence or path splitting;
* root/root-shell reachability;
* residual size or raw residual frontier;
* deleted-vertex adjacency outside the residual;
* empirical bounded search;
* packing or projection of an already bounded menu;
* choosing terminal neighbors post-hoc from a current `(X, deleted X)` witness;
* treating the presence of a per-witness `terminalNeighborCode` field as
  injectivity without a pairwise separation theorem.

## Migration Path

The intended non-circular chain is:

```text
PhysicalPlaquetteGraphResidualFiberTerminalNeighborGeometricSelectorCode1296
  -> PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296
  -> PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorCodeSeparation1296
  -> PhysicalPlaquetteGraphResidualFiberTerminalNeighborCodeSeparation1296
  -> PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominatingMenu1296
  -> PhysicalPlaquetteGraphResidualFiberTerminalNeighborImageCompression1296
```

Only the first arrow is new.  The reverse arrow from `ImageCompression` back to
`SelectorImageBound` remains a projection from an already bounded menu and must
not be used to prove the first arrow.

## Validation

Dashboard-only scope.  No Lean file was edited and no lake build was required.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`.  No status, percentage, README metric,
planner metric, ledger row, or Clay-level claim moved.

## Next Task

Add the Lean interface and bridge:

```text
CODEX-F3-TERMINAL-NEIGHBOR-GEOMETRIC-SELECTOR-CODE-INTERFACE-001
```
