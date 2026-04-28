# F3 residual bookkeeping tag coordinate proof attempt v2.205

Task: `CODEX-F3-PROVE-BOOKKEEPING-TAG-COORDINATE-001`

## Result

No Lean theorem was added.  The target remains:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagCoordinate1296
```

The v2.204 coordinate-first interface and bridge still build, but the current
Lean inventory does not contain a structural bookkeeping/base-zone law proving
that a residual-indexed `Fin 1296` coordinate separates every selector-evidence
admissible terminal-neighbor value.

## Exact no-closure blocker

The missing upstream source is a selector-admissible residual-value separation
theorem, tentatively:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagAdmissibleValueSeparation1296
```

It should provide the proof-relevant fact that, for the v2.121 bookkeeping
residual fibers, a bookkeeping/base-zone coordinate on residual values
separates all values that can appear as `terminalNeighborOfParent residual p`
under `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`
evidence.

This is narrower than full injectivity of the residual subtype into `Fin 1296`
and stronger than merely choosing a `Fin 1296` field.  The current interface
requires the coordinate data before the selector is fixed, so the missing
theorem must explain why that pre-existing coordinate discriminates all
selector-admissible selected values.

## Why existing Lean evidence is insufficient

The available artifacts do not prove the target:

- root-shell codes code first-shell elements of an anchored bucket, not arbitrary
  residual subtype values and not selector-admissible terminal-neighbor values;
- root-neighbor and local-neighbor codes are root/local relative and do not
  give residual bookkeeping/base-zone tag injectivity;
- `terminalNeighborCode : Fin 1296` inside selector data is parent-relative
  evidence, not a residual-subtype coordinate chosen before the selector;
- v2.121 base-aware bookkeeping supplies `deleted`, `parentOf`, `essential`,
  residual image, and residual subset data, but no selected-value separation
  law for a residual bookkeeping coordinate;
- selected-image and bounded-menu paths would produce a code after the selector
  is known, which is explicitly the circular route excluded here.

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
theorem-specific axiom trace is required.  The v2.204 interface/bridge traces
remain:

```text
PhysicalPlaquetteGraphResidualFiberBookkeepingTagCoordinate1296:
  [propext, Classical.choice, Quot.sound]

physicalPlaquetteGraphResidualFiberBookkeepingTagValueSeparation1296_of_residualFiberBookkeepingTagCoordinate1296:
  [propext, Classical.choice, Quot.sound]
```

F3-COUNT remains `CONDITIONAL_BRIDGE`. No status, percentage, README metric,
planner metric, ledger row, vacuity caveat, proof claim, or Clay-level claim
moved.

## Next task

`CODEX-F3-BOOKKEEPING-TAG-ADMISSIBLE-VALUE-SEPARATION-SCOPE-001`

Scope the selector-admissible residual-value separation theorem and its bridge
into `PhysicalPlaquetteGraphResidualFiberBookkeepingTagCoordinate1296`.
