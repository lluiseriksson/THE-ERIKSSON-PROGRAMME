# F3 terminal-neighbor absolute selected-value code scope v2.168

Task: `CODEX-F3-TERMINAL-NEIGHBOR-ABSOLUTE-SELECTED-VALUE-CODE-SCOPE-001`

## Proposed source theorem

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborAbsoluteSelectedValueCode1296
```

Intended no-sorry bridge:

```lean
physicalPlaquetteGraphResidualFiberTerminalNeighborBasepointIndependentCode1296_of_residualFiberTerminalNeighborAbsoluteSelectedValueCode1296
```

Bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborBasepointIndependentCode1296
```

## Scope

The source theorem should be residual-local and indexed by the same v2.121
bookkeeping hypotheses as the existing terminal-neighbor interfaces.  For each
residual fiber it must construct:

- `terminalNeighborOfParent`, assigning each essential parent a terminal
  neighbor in the residual;
- `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` for every
  selected parent/terminal-neighbor pair;
- an absolute value code, preferably of shape
  `{q : ConcretePlaquette physicalClayDimension L // q ∈ residual} → Fin 1296`
  or an equivalent residual-local absolute-value domain, together with a
  selected-value separation theorem:
  if two essential parents have equal absolute codes on their selected terminal
  neighbors, then the selected terminal-neighbor plaquettes are equal.

This is intentionally one step stronger and less circular than the v2.166
`BasepointIndependentCode1296` interface.  The v2.166 interface codes the
selected-image subtype itself.  The new source should produce the absolute code
before treating the selected image as an already bounded or already packaged
object; the bridge then restricts the absolute residual-value code to the
selected-image subtype and obtains `Function.Injective` by the selected-value
separation theorem.

## Bridge burden

Given the absolute-code source, the bridge to
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborBasepointIndependentCode1296`
should:

1. reuse `terminalNeighborOfParent`;
2. reuse the selector-data evidence;
3. define `terminalNeighborValueCode residual q` by applying the absolute
   residual-value code to the selected terminal-neighbor value `q.1`, using
   the image membership witness only to establish `q.1 ∈ residual`;
4. prove injectivity on the selected-image subtype from the pairwise
   selected-value separation clause.

The bridge is projection/restriction only; the source theorem carries the real
mathematical burden.

## Rejected routes

This scope does not treat any of the following as selected-value cardinality or
separation evidence:

- local displacement codes relative to each parent;
- equality of a per-parent `terminalNeighborCode` field;
- local degree;
- residual paths or root/root-shell reachability;
- residual size or raw frontier size;
- deleted-vertex adjacency outside the residual;
- empirical bounded search;
- packing/projection of an already bounded menu or selected image;
- `finsetCodeOfCardLe` applied to an already bounded selected image;
- the v2.161 circular chain
  `SelectorImageBound -> SelectorCodeSeparation -> CodeSeparation -> DominatingMenu -> ImageCompression -> SelectorImageBound`;
- terminal neighbors chosen post-hoc from a current `(X, deleted X)` witness.

## Validation

Dashboard-only scope.  No Lean file was edited, so no `lake build` was required
for this task.

F3-COUNT remains `CONDITIONAL_BRIDGE`.  No status, percentage, README metric,
planner metric, ledger row, vacuity caveat, or Clay-level claim moved.

## Next task

Add the no-sorry Lean interface
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborAbsoluteSelectedValueCode1296`
and, only if it builds without `sorry`, the bridge
`physicalPlaquetteGraphResidualFiberTerminalNeighborBasepointIndependentCode1296_of_residualFiberTerminalNeighborAbsoluteSelectedValueCode1296`.
