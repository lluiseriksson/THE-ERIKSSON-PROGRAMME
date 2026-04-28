# F3 terminal-neighbor basepoint-independent code interface v2.166

Task: `CODEX-F3-TERMINAL-NEIGHBOR-BASEPOINT-INDEPENDENT-CODE-INTERFACE-RETRY-001`

## Result

Added the no-sorry residual-local interface:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborBasepointIndependentCode1296
```

and the no-sorry bridge:

```lean
physicalPlaquetteGraphResidualFiberTerminalNeighborGeometricSelectorCode1296_of_residualFiberTerminalNeighborBasepointIndependentCode1296
```

Bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborGeometricSelectorCode1296
```

## Interface shape

The interface exposes:

- `terminalNeighborOfParent`, indexed by residual and essential parent;
- `terminalNeighborSelectorEvidence`, proving
  `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` for each selected terminal neighbor;
- `terminalNeighborValueCode`, a `Fin 1296` code on the selected terminal-neighbor image as absolute residual values;
- `Function.Injective (terminalNeighborValueCode residual)` for each residual fiber.

This is intentionally stronger than per-parent local displacement coding.  The
code domain is the selected-image subtype itself, so equality of codes separates
selected terminal-neighbor values across different essential parents.

## Bridge

The bridge evaluates the absolute selected-value code at each parent's selected
terminal neighbor, producing the parent-indexed geometric selector code required
by v2.163.  Pairwise selected-value separation follows by injectivity of the
absolute code.

The bridge does not use `finsetCodeOfCardLe` on an already bounded selected
image and does not route through the v2.161 cycle:

```text
SelectorImageBound -> SelectorCodeSeparation -> CodeSeparation -> DominatingMenu -> ImageCompression -> SelectorImageBound
```

## Validation

Command:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result: passed.

New bridge axiom trace:

```text
[propext, Classical.choice, Quot.sound]
```

## Impact

F3-COUNT remains `CONDITIONAL_BRIDGE`.  No percentage, README metric, planner
metric, ledger row, vacuity caveat, or Clay-level claim moved.
