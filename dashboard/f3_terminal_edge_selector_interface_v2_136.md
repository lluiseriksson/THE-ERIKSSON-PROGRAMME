# F3 residual-fiber terminal-edge selector interface v2.136

Task: `CODEX-F3-TERMINAL-EDGE-SELECTOR-INTERFACE-001`

## Result

Added the no-sorry Lean interface:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalTerminalEdgeSelector1296
```

and the projection/repacking bridge:

```lean
physicalPlaquetteGraphResidualFiberCanonicalLastEdgeImageBound1296_of_residualFiberCanonicalTerminalEdgeSelector1296
```

The new data structure is:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalTerminalEdgeData
```

## Lean Locations

```text
YangMills/ClayCore/LatticeAnimalCount.lean:3281
YangMills/ClayCore/LatticeAnimalCount.lean:3504
YangMills/ClayCore/LatticeAnimalCount.lean:3563
YangMills/ClayCore/LatticeAnimalCount.lean:6339
```

## Interface Separation

The interface exposes residual-local canonical path or path-code data separately
from terminal-edge selection:

- `pathSource` and `canonicalPath` record residual-local canonical path data;
- `terminalPred` and `terminalPath` record the selected terminal predecessor
  and residual path to the target;
- the bridge uses `terminalPred` as the v2.132 canonical predecessor;
- the selected predecessor image-cardinality bound remains explicit and applies
  to the terminal predecessor image over each residual fiber.

This does not prove the producer theorem. It only creates the interface and a
clean bridge into:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalLastEdgeImageBound1296
```

## Non-Confusions

The bridge does not construct terminal-edge selectors.

It does not use deleted-vertex adjacency outside the residual.

It does not choose terminal predecessors post-hoc from a current
`(X, deleted X)` witness.

It does not treat root-shell reachability, local degree, raw residual frontier,
residual size, or empirical bounded search as the selected-image cardinality
bound.

## Validation

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

passed.

The new bridge theorem-specific axiom trace is:

```text
[propext, Classical.choice, Quot.sound]
```

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No ledger status, project percentage,
README metric, planner metric, or Clay-level claim moved.

## Next Task

Prove or precisely fail:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalTerminalEdgeSelector1296
```

The proof must construct the residual-local terminal-edge selector and the
selected terminal predecessor image-cardinality bound `<= 1296`; it cannot use
the bridge itself as evidence of the producer.
