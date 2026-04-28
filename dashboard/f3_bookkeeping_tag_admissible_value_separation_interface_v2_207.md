# F3 bookkeeping tag admissible-value separation interface v2.207

Task: `CODEX-F3-BOOKKEEPING-TAG-ADMISSIBLE-VALUE-SEPARATION-INTERFACE-001`

Status: `DONE_INTERFACE_AND_BRIDGE_LANDED_NO_STATUS_MOVE`

## Lean landing

Added the no-sorry Lean interface:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagAdmissibleValueSeparation1296
```

Location:

```text
YangMills/ClayCore/LatticeAnimalCount.lean:4093
```

The interface is relative to the v2.121 bookkeeping residual-fiber hypotheses.
It produces residual-indexed bookkeeping tag code data:

```lean
forall residual,
  PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCodeData
    residual
```

before any fixed `terminalNeighborOfParent` selector is supplied.  Its
separation clause applies to residual values that are selector-admissible via
`Nonempty (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
residual p.1 value)` evidence from an essential parent.

## Bridge landed

Added the no-sorry bridge:

```lean
physicalPlaquetteGraphResidualFiberBookkeepingTagCoordinate1296_of_residualFiberBookkeepingTagAdmissibleValueSeparation1296
```

Location:

```text
YangMills/ClayCore/LatticeAnimalCount.lean:4228
```

Bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagCoordinate1296
```

The bridge is direct repackaging.  Once the caller supplies a fixed
`terminalNeighborOfParent` and selector evidence, each selected value is
admissible by taking the corresponding essential parent and wrapping the
selector-data witness in `Nonempty`; the admissible-value separation clause
then supplies the selected-value equality.

## Explicit non-routes

This interface and bridge do not use:

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

The new `#print axioms` traces are:

```text
YangMills.PhysicalPlaquetteGraphResidualFiberBookkeepingTagAdmissibleValueSeparation1296:
  [propext, Classical.choice, Quot.sound]

YangMills.physicalPlaquetteGraphResidualFiberBookkeepingTagCoordinate1296_of_residualFiberBookkeepingTagAdmissibleValueSeparation1296:
  [propext, Classical.choice, Quot.sound]
```

F3-COUNT remains `CONDITIONAL_BRIDGE`. No status, percentage, README metric,
planner metric, ledger row, vacuity caveat, proof claim, or Clay-level claim
moved.

## Next task

`CODEX-F3-PROVE-BOOKKEEPING-TAG-ADMISSIBLE-VALUE-SEPARATION-001`

Prove `PhysicalPlaquetteGraphResidualFiberBookkeepingTagAdmissibleValueSeparation1296`
or reduce it to the next exact no-closure blocker.
