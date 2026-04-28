# F3 bookkeeping tag admissible-value separation proof attempt v2.208

Task: `CODEX-F3-PROVE-BOOKKEEPING-TAG-ADMISSIBLE-VALUE-SEPARATION-001`

## Result

No Lean theorem was added.  The attempted target remains:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagAdmissibleValueSeparation1296
```

The v2.207 interface and bridge still build:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagAdmissibleValueSeparation1296

physicalPlaquetteGraphResidualFiberBookkeepingTagCoordinate1296_of_residualFiberBookkeepingTagAdmissibleValueSeparation1296
```

The current Lean inventory does not contain a structural residual bookkeeping
tag source that separates all values admissible under
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` evidence from
essential parents.

## Exact no-closure blocker

The next missing upstream source is tentatively:

```lean
PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBookkeepingTagInjection1296
```

It should provide, for the v2.121 bookkeeping residual fibers, a
selector-independent residual bookkeeping/base-zone tag code into `Fin 1296`
and prove that equal tags force equal residual values whenever both values are
admissible through terminal-neighbor selector-data evidence from essential
parents.

Equivalently, the proof needs Lean-level replacements for the informal
bookkeeping ingredients referenced in the creative artifacts:

```text
BookkeepingTagSpace
bookkeepingTagOfResidualVertex
bookkeepingTagIntoFin1296
selector-admissible tag injectivity
```

without deriving the code from a selected image or from a bounded menu.

## Why existing Lean evidence is insufficient

- The v2.121 bookkeeping theorem supplies `deleted`, `parentOf`, `essential`,
  residual images, and `essential residual ⊆ residual`, but it does not expose
  a residual-value bookkeeping tag space or selector-admissible injectivity law.
- Root-shell codes and root-neighbor codes name first-shell or root-local
  witnesses, not residual-subtype bookkeeping tags.
- Local neighbor and local displacement codes are local to a current plaquette
  and do not prove residual-value tag injectivity.
- `terminalNeighborCode : Fin 1296` inside selector data is witness-relative
  and parent-relative; equality of those codes is not absolute selected-value
  equality across essential parents.
- `finsetCodeOfCardLe` and selected-image or menu cardinality routes would
  build the code after the selected image is known, which is the circular route
  excluded by this chain.

## Rejected routes

This attempt does not use:

- selected-image cardinality;
- bounded menu cardinality;
- empirical search;
- `finsetCodeOfCardLe`;
- the v2.161 selector-image cycle;
- root-shell codes as residual-subtype bookkeeping tag injectivity;
- local neighbor codes as residual-subtype bookkeeping tag injectivity;
- local displacement codes as residual-subtype bookkeeping tag injectivity;
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
theorem-specific axiom trace is required.  The v2.207 interface and bridge
traces remain no larger than:

```text
[propext, Classical.choice, Quot.sound]
```

F3-COUNT remains `CONDITIONAL_BRIDGE`. No status, percentage, README metric,
planner metric, ledger row, vacuity caveat, proof claim, or Clay-level claim
moved.

## Next task

`CODEX-F3-SELECTOR-ADMISSIBLE-BOOKKEEPING-TAG-INJECTION-SCOPE-001`

Scope the structural selector-admissible bookkeeping-tag injection theorem and
its bridge into
`PhysicalPlaquetteGraphResidualFiberBookkeepingTagAdmissibleValueSeparation1296`.
