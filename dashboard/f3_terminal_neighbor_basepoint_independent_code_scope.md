# F3 residual terminal-neighbor basepoint-independent code scope (v2.165)

Task: `CODEX-F3-TERMINAL-NEIGHBOR-BASEPOINT-INDEPENDENT-CODE-SCOPE-001`

## Result

Scoped the next residual-local source theorem:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborBasepointIndependentCode1296
```

Its exact bridge target is:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborGeometricSelectorCode1296
```

with intended bridge:

```lean
physicalPlaquetteGraphResidualFiberTerminalNeighborGeometricSelectorCode1296_of_residualFiberTerminalNeighborBasepointIndependentCode1296
```

## Why This Is Sharper Than v2.164

v2.164 showed that local displacement codes are base-relative: equal local
codes from different essential parents do not identify the same absolute
terminal-neighbor plaquette.

The new theorem must therefore code selected terminal-neighbor values as
absolute residual values, not as per-parent displacements.

## Proposed Interface Shape

The theorem should quantify over the same v2.121 bookkeeping data as
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborGeometricSelectorCode1296`:

- `root`, `k`;
- `deleted`, `parentOf`;
- `essential`;
- the safe-deletion choice hypothesis;
- the residual-fiber image identity for `essential`;
- `essential residual ⊆ residual`.

It should construct:

```lean
terminalNeighborOfParent :
  ∀ residual,
    (p : {p : ConcretePlaquette physicalClayDimension L //
      p ∈ essential residual}) →
      {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}
```

and residual-local selector evidence:

```lean
terminalNeighborSelectorEvidence :
  ∀ residual,
    (p : {p : ConcretePlaquette physicalClayDimension L //
      p ∈ essential residual}) →
      PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
        residual p.1 (terminalNeighborOfParent residual p)
```

Then define the selected-value image:

```lean
selectedTerminalNeighborImage residual :=
  (essential residual).attach.image
    (fun p => (terminalNeighborOfParent residual p).1)
```

and expose a basepoint-independent code on selected values:

```lean
terminalNeighborValueCode :
  ∀ residual,
    {q : ConcretePlaquette physicalClayDimension L //
      q ∈ selectedTerminalNeighborImage residual} → Fin 1296
```

with injectivity:

```lean
∀ residual, Function.Injective (terminalNeighborValueCode residual)
```

This code is basepoint-independent because the domain is the selected terminal
neighbor value itself, not the current parent and not a displacement from the
current parent.

## Bridge To Geometric Selector Code

The bridge into
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborGeometricSelectorCode1296`
should:

1. reuse `terminalNeighborOfParent`;
2. reuse `terminalNeighborSelectorEvidence`;
3. define the parent-indexed geometric code by applying
   `terminalNeighborValueCode` to the selected value of that parent;
4. prove pairwise selected-value separation from injectivity of the value code.

The bridge does not need the selected-image cardinality bound and must not
derive the value code by `finsetCodeOfCardLe` on an already bounded selected
image.

## Non-Substitutes

This scope explicitly rejects:

- per-parent local displacement codes;
- equality of `terminalNeighborCode` fields without a selected-value
  injectivity theorem;
- local degree or local neighbor existence;
- residual path existence or path splitting;
- root or root-shell reachability;
- residual size or raw residual frontier;
- deleted-vertex adjacency outside the residual;
- empirical bounded search;
- packing or projection of an already bounded menu;
- `finsetCodeOfCardLe` on an already bounded selected image;
- the v2.161 circular route:

```text
SelectorImageBound -> SelectorCodeSeparation -> CodeSeparation
  -> DominatingMenu -> ImageCompression -> SelectorImageBound
```

- post-hoc terminal neighbors chosen from a current `(X, deleted X)` witness.

## Validation

Dashboard-only scope.  No Lean file was edited and no lake build was required.

F3-COUNT remains `CONDITIONAL_BRIDGE`.  No status, percentage, README metric,
planner metric, ledger row, or Clay-level claim moved.

## Next Task

Add the no-sorry Lean interface and bridge:

```text
CODEX-F3-TERMINAL-NEIGHBOR-BASEPOINT-INDEPENDENT-CODE-INTERFACE-001
```

