# F3 canonical last-edge bridge axiom frontier v2.133

Task: `CODEX-F3-CANONICAL-LAST-EDGE-BRIDGE-AXIOM-FRONTIER-001`

## Result

The axiom-frontier blocker reported in v2.132 was isolated as a stale/failed
iteration artifact.  Replaying the same bridge in a clean imported environment
gave:

```text
'test_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The bridge was then added to Lean:

```lean
physicalPlaquetteGraphResidualFiberTerminalPredecessorImageBound1296_of_residualFiberCanonicalLastEdgeImageBound1296
```

Location:

```text
YangMills/ClayCore/LatticeAnimalCount.lean:3539
```

Its module `#print axioms` trace is:

```text
[propext, Classical.choice, Quot.sound]
```

## What The Bridge Does

The bridge projects the canonical residual last-edge datum:

```lean
(canonicalLastEdgeData residual p).predecessor
```

as the terminal predecessor required by
`PhysicalPlaquetteGraphResidualFiberTerminalPredecessorImageBound1296`.

It passes through:

- non-singleton last-edge adjacency;
- the canonical target and `target_eq`;
- the induced residual walk packaged in the canonical datum;
- the selected predecessor image cardinality bound.

## Non-Confusions

The bridge does not construct canonical paths.

It does not choose terminal predecessors post-hoc from a current
`(X, deleted X)` witness.

It does not use deleted-vertex adjacency outside the residual.

It does not treat root reachability, local degree, residual size, raw frontier
growth, or empirical search as a selected-image bound.

## Validation

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

passed.

The new bridge theorem's axiom trace is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

## Next Exact Task

The bridge chain now reaches:

```text
PhysicalPlaquetteGraphResidualFiberCanonicalLastEdgeImageBound1296
  -> PhysicalPlaquetteGraphResidualFiberTerminalPredecessorImageBound1296
```

The remaining producer theorem is:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalLastEdgeImageBound1296
```

Recommended next task:

```text
CODEX-F3-PROVE-RESIDUAL-FIBER-CANONICAL-LAST-EDGE-IMAGE-BOUND-001
```

## Non-Claims

This task does not prove:

- `PhysicalPlaquetteGraphResidualFiberCanonicalLastEdgeImageBound1296`;
- `PhysicalPlaquetteGraphResidualFiberTerminalPredecessorImageBound1296`;
- any decoder theorem or compression to older constants.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No ledger status, project percentage,
README metric, planner metric, or Clay-level claim moved.
