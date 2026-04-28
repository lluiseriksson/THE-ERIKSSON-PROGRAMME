# F3 walk terminal-edge selected-image interface (v2.139)

Task: `CODEX-F3-WALK-TERMINAL-EDGE-IMAGE-BOUND-INTERFACE-001`

## Result

Added the no-sorry Lean data structure:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalWalkTerminalEdgeData
```

Added the no-sorry Lean Prop/interface:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalWalkTerminalEdgeImageBound1296
```

and proved the projection bridge:

```lean
physicalPlaquetteGraphResidualFiberCanonicalTerminalEdgeSelector1296_of_residualFiberCanonicalWalkTerminalEdgeImageBound1296
```

with target:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalTerminalEdgeSelector1296
```

## Lean Locations

```text
YangMills/ClayCore/LatticeAnimalCount.lean:3305
YangMills/ClayCore/LatticeAnimalCount.lean:3591
YangMills/ClayCore/LatticeAnimalCount.lean:3650
YangMills/ClayCore/LatticeAnimalCount.lean:6464
```

## Interface Separation

The new structure exposes residual-local canonical walk/path data separately from
terminal-edge extraction:

- `walkSource` and `canonicalWalk` record the full residual-local canonical walk;
- `terminalPred` and `terminalSuffix` record the extracted terminal predecessor
  and residual suffix to the target;
- `terminalCode` is the selected predecessor code into `Fin 1296`;
- the Prop keeps the selected terminal-predecessor image-cardinality bound
  `<= 1296` explicit over each residual fiber.

The bridge only forgets the stronger field names into the v2.136
`PhysicalPlaquetteGraphResidualFiberCanonicalTerminalEdgeData`.

## Non-Confusions

The interface does not assert that path existence alone proves the image bound.

It does not use root/root-shell reachability, local degree, residual size, raw
frontier growth, deleted-vertex adjacency outside the residual, empirical
bounded search, or packing an already bounded menu as a substitute for the
selected-image cardinality bound.

It also does not prove the producer theorem. The remaining mathematical target
is to construct the residual-local walk terminal-edge data and image bound.

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
PhysicalPlaquetteGraphResidualFiberCanonicalWalkTerminalEdgeImageBound1296
```

The proof must construct the residual-local canonical walk/path data, terminal
edge extraction, last-edge adjacency, residual suffix evidence, and selected
terminal-predecessor image bound `<= 1296` without post-hoc deleted-vertex data.
