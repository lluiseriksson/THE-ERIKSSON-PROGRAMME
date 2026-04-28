# F3 bookkeeping tag value-separation attempt v2.202

Task: `CODEX-F3-PROVE-BOOKKEEPING-TAG-VALUE-SEPARATION-001`

## Result

No Lean theorem was added.  The target remains:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueSeparation1296
```

The v2.201 interface and bridge still build, but the current Lean inventory
does not contain a structural residual bookkeeping/base-zone tag coordinate on
all residual subtype values whose equality separates the selected
terminal-neighbor values for an arbitrary fixed residual-local
`terminalNeighborOfParent` selector.

## Exact no-closure blocker

The missing upstream source is a genuine residual-value bookkeeping coordinate
theorem, tentatively:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagCoordinate1296
```

It should provide, for every v2.121 bookkeeping residual fiber, a structural
`Fin 1296` tag on the whole residual subtype together with the theorem that
this tag separates the terminal-neighbor values selected by any fixed
selector/evidence pair accepted by
`PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueSeparation1296`.

The key missing ingredient is not merely a `Fin 1296` field: it is a
proof-relevant reason why equality of the residual bookkeeping coordinate
forces equality of the selected residual values.

## Why existing Lean evidence is insufficient

Existing code-like artifacts do not prove the target:

- root-shell codes such as
  `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellCode1296_injective`
  code first-shell elements of an anchored bucket and are built from a shell
  cardinality bound; they do not code arbitrary residual subtype values;
- local neighbor/root-neighbor codes are local or root-relative and do not give
  a residual-subtype bookkeeping coordinate;
- `terminalNeighborCode : Fin 1296` inside
  `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` is
  selector evidence attached to a parent/selection and cannot be used as
  residual-value tag injectivity;
- v2.121 bookkeeping
  `physicalPlaquetteGraph_baseAwareTerminalPredecessorBookkeeping1296` supplies
  `deleted`, `parentOf`, `essential`, residual image, and residual subset
  information, but no residual-value tag map with injectivity/separation.

## Rejected routes

This attempt does not use:

- selected-image cardinality;
- bounded menu cardinality;
- empirical search;
- `finsetCodeOfCardLe`;
- the v2.161 selector-image cycle;
- root-shell codes as residual-subtype tag injectivity;
- local neighbor codes as residual-subtype tag injectivity;
- local displacement codes;
- parent-relative `terminalNeighborCode` equality;
- deleted `X` as a residual terminal neighbor for
  `residual = X.erase (deleted X)`.

## Validation

Command:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result: passed.

No new theorem was introduced in this no-closure attempt, so no new
theorem-specific axiom trace is required beyond the v2.201 interface/bridge
traces already recorded:

```text
PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueSeparation1296:
  [propext, Classical.choice, Quot.sound]

physicalPlaquetteGraphResidualFiberBookkeepingTagValueCodeSource1296_of_residualFiberBookkeepingTagValueSeparation1296:
  [propext, Classical.choice, Quot.sound]
```

F3-COUNT remains `CONDITIONAL_BRIDGE`. No status, percentage, README metric,
planner metric, ledger row, vacuity caveat, proof claim, or Clay-level claim
moved.

## Next task

`CODEX-F3-RESIDUAL-BOOKKEEPING-TAG-COORDINATE-SCOPE-001`

Scope the structural residual bookkeeping/base-zone coordinate theorem and its
bridge into `PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueSeparation1296`.
