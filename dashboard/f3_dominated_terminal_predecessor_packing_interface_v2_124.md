# F3 dominated terminal-predecessor packing interface v2.124

Task: `CODEX-F3-DOMINATED-TERMINAL-PREDECESSOR-PACKING-INTERFACE-001`

## Result

Codex added the no-sorry Lean interface
`PhysicalPlaquetteGraphResidualDominatedTerminalPredecessorPacking1296` and
proved the narrow packing theorem
`physicalPlaquetteGraph_residualDominatedTerminalPredecessorPacking1296`.

The theorem only packs an explicit residual-local selected terminal-predecessor
menu into an injective `Fin 1296` code when `terminalPredMenu.card <= 1296`.
It does not infer last-edge domination from arbitrary `essential subset
residual` data.  Last-edge domination evidence, residual path evidence, menu
membership, and the menu cardinality bound are inputs.

## Lean identifiers

- `PhysicalPlaquetteGraphResidualDominatedTerminalPredecessorPacking1296`
  at `YangMills/ClayCore/LatticeAnimalCount.lean:3380`
- `physicalPlaquetteGraph_residualDominatedTerminalPredecessorPacking1296`
  at `YangMills/ClayCore/LatticeAnimalCount.lean:4973`
- `#print axioms physicalPlaquetteGraph_residualDominatedTerminalPredecessorPacking1296`
  at `YangMills/ClayCore/LatticeAnimalCount.lean:5889`

## Validation

`lake build YangMills.ClayCore.LatticeAnimalCount` passed.

The theorem-specific axiom trace is:

```text
[propext, Classical.choice, Quot.sound]
```

## Migration path

The v2.114 interface
`PhysicalPlaquetteGraphResidualTerminalPredecessorDomination1296` remains too
strong because arbitrary `essential subset residual` data does not imply
last-edge domination.

The next target should produce residual-fiber-specific domination data:
an explicit `terminalPredMenu`, a `terminalPredOfParent` selector, residual
path evidence, last-edge domination evidence, and `terminalPredMenu.card <=
1296`.  Those data can feed the v2.124 packing theorem and the v2.121
base-aware bookkeeping route toward a corrected bridge into
`PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296`.

## Non-claims

This is interface/packing evidence only.  It does not prove the old v2.114
domination theorem, does not compress any decoder alphabet, and does not move
`F3-COUNT` out of `CONDITIONAL_BRIDGE`.  No project percentage or Clay-level
claim moved.
