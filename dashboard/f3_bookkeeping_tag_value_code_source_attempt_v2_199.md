# F3 residual bookkeeping tag value-code source attempt v2.199

Task: `CODEX-F3-PROVE-BOOKKEEPING-TAG-VALUE-CODE-SOURCE-001`

## Result

No Lean theorem was added.  The target remains:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueCodeSource1296
```

The v2.198 interface and bridge still build, but the current Lean inventory does
not contain a structural source for the required residual-value bookkeeping tag
data:

```lean
∀ residual,
  PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCodeData
    residual
```

together with selected-value separation for a fixed
`terminalNeighborOfParent`.

## Exact no-closure blocker

The missing upstream theorem is a genuine residual-value bookkeeping tag
injection/separation source, tentatively:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueSeparation1296
```

It should provide, for every v2.121 bookkeeping residual fiber and fixed
selector, a bookkeeping/base-zone tag code on residual values whose equality
separates selected terminal-neighbor values.  This source must be structural:
the code must be defined before considering the selected image.

## Why existing Lean evidence is insufficient

Existing candidate code sources are not enough:

- root-shell codes such as
  `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellCode1296_injective`
  code first-shell elements of an anchored bucket, not arbitrary residual
  subtype values;
- v2.121 bookkeeping
  `physicalPlaquetteGraph_baseAwareTerminalPredecessorBookkeeping1296` provides
  `deleted`, `parentOf`, `essential`, residual image, and residual subset data,
  but no residual-value tag code;
- selector-source evidence provides `terminalNeighborOfParent` and
  `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`, but that
  data only contains a per-parent `terminalNeighborCode : Fin 1296`.

Using the per-parent `terminalNeighborCode` as the residual-value tag would be
the forbidden parent-relative-code route.  Likewise, manufacturing a code by
bounding the selected image would be selected-image cardinality, and using
`finsetCodeOfCardLe` on such an image would recreate the prohibited v2.161
cycle.

## Rejected routes

This attempt does not use:

- selected-image cardinality;
- bounded menu cardinality;
- empirical search;
- `finsetCodeOfCardLe`;
- the v2.161 selector-image cycle;
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
theorem-specific axiom trace is required beyond the v2.198 interface/bridge
traces already recorded.

F3-COUNT remains `CONDITIONAL_BRIDGE`. No status, percentage, README metric,
planner metric, ledger row, vacuity caveat, proof claim, or Clay-level claim
moved.

## Next task

`CODEX-F3-BOOKKEEPING-TAG-VALUE-SEPARATION-SCOPE-001`

Scope the structural residual-value bookkeeping tag separation theorem and its
bridge into `PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueCodeSource1296`.
