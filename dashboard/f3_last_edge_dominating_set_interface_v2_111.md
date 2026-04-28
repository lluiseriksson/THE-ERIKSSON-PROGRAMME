# F3 Last-Edge Dominating-Set Interface v2.111

Task: `CODEX-F3-LAST-EDGE-DOMINATING-SET-INTERFACE-001`

## Result

Codex added the Lean interface:

```lean
PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296
```

and the repacking bridge:

```lean
physicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgePredecessorSelector1296_of_residualLastEdgeDominatingSetBound1296
```

The interface is deliberately sharper than the v2.107 selector. It exposes:

- a residual-only selected terminal-predecessor menu `terminalPredMenu residual`;
- selected terminal predecessors `terminalPredOfParent residual p` living in the residual;
- an injective residual-indexed code `terminalPredCode residual : ... -> Fin 1296`;
- residual-local path evidence from each selected predecessor to the essential parent;
- last-edge domination for non-singleton residuals.

The bridge only repacks those data into
`PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgePredecessorSelector1296`.
It does not prove the dominating-set existence theorem.

## Validation

`lake build YangMills.ClayCore.LatticeAnimalCount` passed.

The new bridge axiom trace is:

```text
[propext, Classical.choice, Quot.sound]
```

The `#print axioms` line was added for:

```lean
physicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgePredecessorSelector1296_of_residualLastEdgeDominatingSetBound1296
```

## Non-Claims

This task does not prove:

- `PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296`,
- `PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgePredecessorSelector1296`,
- `PhysicalPlaquetteGraphDeletedVertexDecoderStep1296x1296x1296`,
- compression to older `1296` or `1296x1296` constants.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No ledger row, project percentage,
README metric, planner metric, or Clay-level claim moved.

## Next Target

```text
CODEX-F3-PROVE-LAST-EDGE-DOMINATING-SET-BOUND-001
```

Prove or precisely fail `PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296`.
