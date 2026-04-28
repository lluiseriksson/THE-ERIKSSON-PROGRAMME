# F3 residual-fiber terminal-predecessor domination interface v2.126

Task: `CODEX-F3-RESIDUAL-FIBER-TERMINAL-PREDECESSOR-DOMINATION-INTERFACE-001`

## Result

Codex added the no-sorry Lean interface:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalPredecessorDomination1296
```

and proved the bridge:

```lean
physicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296_of_baseAwareBookkeeping_of_residualFiberTerminalPredecessorDomination1296_of_packing1296
```

The interface quantifies over the `deleted`, `parentOf`, and `essential`
bookkeeping data and the actual v2.116/v2.121 bookkeeping clauses.  It then
asks for explicit residual-fiber terminal-predecessor data for each residual:

- `terminalPredMenu`;
- `terminalPredOfParent`;
- `terminalPredMenu ⊆ residual`;
- selected-image identity;
- selected-menu membership;
- last-edge domination evidence for non-singleton residuals;
- residual path evidence;
- `terminalPredMenu.card <= 1296`.

The bridge composes:

1. `PhysicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296`;
2. `PhysicalPlaquetteGraphResidualFiberTerminalPredecessorDomination1296`;
3. `PhysicalPlaquetteGraphResidualDominatedTerminalPredecessorPacking1296`;

to produce `PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296`.

## Lean identifiers

- `PhysicalPlaquetteGraphResidualFiberTerminalPredecessorDomination1296`
  at `YangMills/ClayCore/LatticeAnimalCount.lean:3419`
- `physicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296_of_baseAwareBookkeeping_of_residualFiberTerminalPredecessorDomination1296_of_packing1296`
  at `YangMills/ClayCore/LatticeAnimalCount.lean:3739`
- `#print axioms physicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296_of_baseAwareBookkeeping_of_residualFiberTerminalPredecessorDomination1296_of_packing1296`
  at `YangMills/ClayCore/LatticeAnimalCount.lean:6024`

## Validation

`lake build YangMills.ClayCore.LatticeAnimalCount` passed.

The bridge theorem-specific axiom trace is:

```text
[propext, Classical.choice, Quot.sound]
```

## Non-confusions

This interface is the producer target, not the v2.124 packing theorem.  It
does not prove the producer and does not infer last-edge domination from
arbitrary `essential subset residual` data.  The producer remains responsible
for constructing the selected terminal-predecessor image over the
bookkeeping fiber.

The target is not a raw residual-frontier bound, not a residual-cardinality
bound, not a local-degree bound for one fixed predecessor, and not
first-shell/root reachability.

## Recommended next task

```text
CODEX-F3-PROVE-RESIDUAL-FIBER-TERMINAL-PREDECESSOR-DOMINATION-001
```

Attempt to prove `PhysicalPlaquetteGraphResidualFiberTerminalPredecessorDomination1296`
or reduce it to the next exact blocker.  The proof must construct the explicit
selected terminal-predecessor menu for bookkeeping fibers and must not choose
terminal predecessors post-hoc from a current `(X, deleted X)` witness.

## Non-claims

This task does not prove `PhysicalPlaquetteGraphResidualFiberTerminalPredecessorDomination1296`,
does not prove `PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296`
unconditionally, does not compress any decoder alphabet, and does not move
`F3-COUNT` out of `CONDITIONAL_BRIDGE`.  No ledger status, project percentage,
README metric, planner metric, or Clay-level claim moved.
