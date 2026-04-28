# F3 terminal-predecessor domination interface v2.114

**Task:** `CODEX-F3-TERMINAL-PREDECESSOR-DOMINATION-INTERFACE-001`  
**Date:** 2026-04-27  
**Status:** interface landed; bridge deferred without status movement.

## Lean interface landed

Codex added the residual-only graph domination interface:

```lean
PhysicalPlaquetteGraphResidualTerminalPredecessorDomination1296
```

Location:

```text
YangMills/ClayCore/LatticeAnimalCount.lean:3346
```

The interface takes only:

```text
residual : Finset (ConcretePlaquette physicalClayDimension L)
essential : Finset (ConcretePlaquette physicalClayDimension L)
essential subset residual
```

and asks for:

- a residual-only `terminalPredMenu`;
- a `terminalPredOfParent` map from essential parents into residual predecessors;
- an injective `terminalPredCode : terminalPredMenu -> Fin 1296`;
- equality of the selected menu with the image of `terminalPredOfParent`;
- last-edge domination for non-singleton residuals;
- induced residual path evidence from each selected predecessor to its parent.

This isolates the graph-theoretic terminal-predecessor domination burden from
the base-aware deletion bookkeeping carried by
`PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296`.

## Bridge status

The intended bridge name remains:

```lean
physicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296_of_terminalPredecessorDomination1296
```

The bridge was not added in this task. The new pure residual interface has no
`X`, deleted-vertex witness, safe-deletion proof, `parentOf`, or essential-parent
construction. Deriving `PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296`
directly from it would reintroduce exactly the base-aware deletion bookkeeping
that v2.113 separated out.

So the precise remaining blocker is a base-aware bookkeeping bridge theorem
that constructs the residual/essential data and proves `essential subset residual`
from the current F3 safe-deletion hypotheses, without choosing terminal
predecessors post-hoc from `(X, deleted X)`.

## Validation

Command run:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result: passed.

No new theorem was introduced by this task; the Lean addition is a `def ... :
Prop`, so there is no new theorem-specific `#print axioms` trace to expand.

## Honesty constraints

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No ledger row, project percentage,
README metric, planner metric, or Clay-level claim moved.

## Recommended next task

`CODEX-F3-BASEAWARE-TERMINAL-DOMINATION-BRIDGE-SCOPE-001`

Scope the exact base-aware deletion/parent bookkeeping theorem needed to combine
`PhysicalPlaquetteGraphResidualTerminalPredecessorDomination1296` with
`PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296`, without
collapsing the residual-only domination theorem back into the full v2.111
interface.
