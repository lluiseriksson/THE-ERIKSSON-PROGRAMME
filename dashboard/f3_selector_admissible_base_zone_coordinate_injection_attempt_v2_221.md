# F3 selector-admissible base-zone coordinate injection attempt v2.221

Task: `CODEX-F3-PROVE-SELECTOR-ADMISSIBLE-BASE-ZONE-COORDINATE-INJECTION-001`

Status: `DONE_NO_CLOSURE_BASE_ZONE_COORDINATE_SOURCE_MISSING`

## Target

Attempt to prove:

```lean
PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296
```

from the current Lean/dashboard state after v2.220 landed the no-sorry interface
and bridge into:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296
```

## Result

No no-sorry proof was added.  The exact next no-closure blocker is a structural
selector-independent base-zone coordinate source theorem, tentatively:

```lean
PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296
```

It must provide, for each v2.121 bookkeeping residual fiber, a residual
bookkeeping/base-zone coordinate source on the whole residual subtype, an
encoding into `Fin 1296`, and selected-admissible injectivity for residual values
carrying `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`
evidence from essential parents.

## Why current Lean does not close it

The v2.220 interface correctly isolates the needed data:

- a selector-independent coordinate space for every residual;
- a coordinate extractor on the whole residual subtype;
- a coordinate encoding into `Fin 1296`;
- selected-admissible injectivity for values with selector-data evidence.

The available upstream Lean evidence supplies residual fibers, essential-parent
bookkeeping, selector data, non-singleton residual walk-split closure, and
root-shell/local-neighbor/local-displacement coding facts.  None of those
construct a selector-independent residual-value base-zone coordinate extractor
or prove that equal encoded base-zone coordinates force equality of
selector-admissible residual values.

Using the residual subtype itself as the coordinate space would still require an
unavailable injection of arbitrary residual values into `Fin 1296`.  Using
root-shell, local-neighbor, local-displacement, or parent-relative
`terminalNeighborCode` data would prove a different statement and is explicitly
outside the admissible route.

## Rejected routes

This attempt did not use selected-image cardinality, bounded menu cardinality,
empirical bounded search, `finsetCodeOfCardLe`, the v2.161 circular chain,
root-shell/local-neighbor/local-displacement codes as residual-subtype
bookkeeping/base-zone injectivity, parent-relative `terminalNeighborCode`
equality, or the deleted-X shortcut for `residual = X.erase (deleted X)`.

## Validation

- `lake build YangMills.ClayCore.LatticeAnimalCount` passed.
- No new theorem was added in this no-closure attempt.
- Existing v2.220 interface and bridge axiom traces remain within
  `[propext, Classical.choice, Quot.sound]`.
- F3-COUNT remains `CONDITIONAL_BRIDGE`; no status, percentage, README metric,
  planner metric, ledger row, proof claim beyond this no-closure analysis, or
  Clay-level claim moved.

## Suggested next task

Use the already READY task:

```text
CODEX-F3-BASE-ZONE-COORDINATE-CANDIDATE-LEMMA-INVENTORY-001
```

to inventory whether any existing Lean lemma can serve as the missing
`PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296`
or to record a sharper blocker before scoping a new interface.
