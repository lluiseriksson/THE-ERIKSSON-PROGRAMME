# F3 residual canonical terminal-suffix image interface (v2.142)

Task: `CODEX-F3-TERMINAL-SUFFIX-IMAGE-BOUND-INTERFACE-001`

## Result

Added the no-sorry Lean data structure:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalTerminalSuffixData
```

Added the no-sorry Lean Prop/interface:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalTerminalSuffixImageBound1296
```

and proved the projection bridge:

```lean
physicalPlaquetteGraphResidualFiberCanonicalWalkTerminalEdgeImageBound1296_of_residualFiberCanonicalTerminalSuffixImageBound1296
```

with target:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalWalkTerminalEdgeImageBound1296
```

## Lean locations

```text
YangMills/ClayCore/LatticeAnimalCount.lean:3329
YangMills/ClayCore/LatticeAnimalCount.lean:3684
YangMills/ClayCore/LatticeAnimalCount.lean:3738
YangMills/ClayCore/LatticeAnimalCount.lean:6590
```

## Interface separation

The new structure exposes terminal-suffix data more finely than v2.139:

- `source` and `canonicalWalk` record the residual-local canonical walk source
  and walk to the target;
- `prefixToTerminalPred` records residual-local path/walk evidence from the
  source to the selected terminal predecessor;
- `terminalPred` and `terminalSuffix` record the selected predecessor and suffix
  to the essential parent;
- `terminalSuffix_is_last_edge` carries the final-edge adjacency proof inside
  the residual;
- `terminalCode` remains the `Fin 1296` selected-predecessor code.

The Prop keeps the selected terminal-predecessor image-cardinality bound
`<= 1296` explicit over each residual fiber.

The bridge only forgets `prefixToTerminalPred` and repacks the remaining fields
into `PhysicalPlaquetteGraphResidualFiberCanonicalWalkTerminalEdgeData`.

## Non-confusions

The interface does not assert that path existence alone proves the selected-image
bound.

It does not use root/root-shell reachability, local degree, residual size, raw
frontier growth, deleted-vertex adjacency outside the residual, empirical
bounded search, or packing an already bounded menu as a substitute for the
selected-image cardinality bound.

It also does not prove the producer theorem. The remaining mathematical target
is to construct the residual-local terminal-suffix data and selected-image bound.

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

## Next task

Prove or precisely fail:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalTerminalSuffixImageBound1296
```

The proof must construct residual-local terminal-suffix data and selected
terminal-predecessor image cardinality `<= 1296` without post-hoc
deleted-vertex data.
