# F3 base-aware bookkeeping interface v2.116

**Task:** `CODEX-F3-BASEAWARE-BOOKKEEPING-INTERFACE-001`  
**Date:** 2026-04-27  
**Status:** Lean interface and two-input bridge landed; no F3-COUNT status movement.

## Lean identifiers landed

```lean
PhysicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296
```

Location:

```text
YangMills/ClayCore/LatticeAnimalCount.lean:3380
```

This is the base-aware bookkeeping interface.  It carries only:

- `deleted`;
- `parentOf`;
- `essential`;
- current-bucket safe-deletion and parent clauses;
- the essential-parent fiber identity;
- `essential residual subset residual`.

It does not contain terminal predecessor menus, terminal predecessor codes,
terminal paths, selected-image bounds, or decoder compression claims.

```lean
physicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296_of_baseAwareBookkeeping_of_terminalPredecessorDomination1296
```

Location:

```text
YangMills/ClayCore/LatticeAnimalCount.lean:3503
```

This bridge takes two inputs:

```lean
hbook :
  PhysicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296

hterminal :
  PhysicalPlaquetteGraphResidualTerminalPredecessorDomination1296
```

and repacks them into:

```lean
PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296
```

The bridge applies `hterminal` separately to each
`(residual, essential residual)` supplied by `hbook`; terminal predecessor
selection remains residual-only and is not chosen from a current `(X, deleted X)`
witness.

## Validation

Command run:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result: passed.

The new bridge has this axiom trace:

```text
YangMills.physicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296_of_baseAwareBookkeeping_of_terminalPredecessorDomination1296
depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Remaining proof burden

The next theorem to prove or precisely fail is:

```lean
PhysicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296
```

That proof must construct the `deleted`, `parentOf`, and `essential` data,
including `essential residual subset residual`, from the existing F3 safe-deletion
and residual-fiber APIs.  It must not prove terminal predecessor domination by
choosing predecessors post-hoc from `(X, deleted X)`.

## Non-claims

This task does not prove:

- `PhysicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296`;
- `PhysicalPlaquetteGraphResidualTerminalPredecessorDomination1296`;
- `PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296` unconditionally;
- any old `Fin 1296` or product-symbol decoder compression;
- F3-COUNT closure.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No ledger row, project percentage,
README metric, planner metric, or Clay-level claim moved.
