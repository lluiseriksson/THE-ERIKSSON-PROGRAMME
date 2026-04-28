# F3 Base-Zone Residual Value Code Separation Scope

Task: `CODEX-F3-BASE-ZONE-RESIDUAL-VALUE-CODE-SEPARATION-SCOPE-001`
Status: `DONE_SCOPE_DELIVERED_NO_LEAN_NO_STATUS_MOVE`
Timestamp: `2026-04-28T06:25:00Z`

## Scoped Theorem

Tentative upstream theorem:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSeparation1296
```

Exact bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealization1296
```

Expected bridge name:

```lean
physicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealization1296_of_baseZoneResidualValueCodeSeparation1296
```

## Purpose

The v2.233 proof attempt showed that the v2.232 realization interface can be
populated by a trivial realization carrier only after one has the real
mathematical content: a selector-independent residual-value code into `Fin 1296`
on the whole residual subtype, plus selected-admissible equality-reflection for
residual values carrying terminal-neighbor selector data evidence from essential
parents.

This scope isolates exactly that missing separation principle.  It is upstream
of `PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealization1296`
and is not a restatement of the realization interface: it removes the
realization/certificate carrier and exposes only the residual-value code and
its equality-reflection law.

## Proposed Data Shape

The Lean interface should follow the v2.232/v2.233 parameter shape and produce
data of the following form:

```text
structure
  PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSeparationData
    {L : Nat} [NeZero L]
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) ->
        Finset (ConcretePlaquette physicalClayDimension L)) where
  residualValueCode :
    forall residual,
      {q : ConcretePlaquette physicalClayDimension L // q in residual} ->
        Fin 1296
  selectorAdmissible_code_injective :
    forall residual
      (a b : {q : ConcretePlaquette physicalClayDimension L // q in residual}),
      (exists p : {p : ConcretePlaquette physicalClayDimension L // p in essential residual},
        Nonempty
          (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
            residual p.1 a.1)) ->
      (exists p : {p : ConcretePlaquette physicalClayDimension L // p in essential residual},
        Nonempty
          (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
            residual p.1 b.1)) ->
      residualValueCode residual a = residualValueCode residual b ->
        a.1 = b.1
```

The Prop-level theorem should quantify over the same v2.121 bookkeeping
residual-fiber parameters as
`PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealization1296`
and return `Nonempty` separation data under the same residual-fiber hypotheses.

## Bridge Into v2.232

The expected bridge into
`PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealization1296`
should be pure erasure/repackaging:

1. obtain separation data from
   `PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSeparation1296`;
2. instantiate `residualValueCodeRealization` as `Unit`;
3. set `residualValueCodeRealizationOfValue residual q := ()`;
4. use `True` or the unique `Unit` witness for realization validity;
5. define `residualValueCodeOfRealization residual q ()` by the supplied
   `residualValueCode residual q`;
6. prove realization-choice stability by cases on `Unit`;
7. discharge `selectorAdmissible_realizedCode_injective` using the supplied
   `selectorAdmissible_code_injective`.

The bridge must not add mathematical content beyond erasing the trivial
realization layer.

## Explicitly Rejected Routes

This scope does not use or authorize:

- selected-image cardinality;
- bounded menu cardinality;
- empirical search;
- `finsetCodeOfCardLe`;
- root-shell codes as residual-subtype injectivity;
- local-neighbor or local-displacement codes as residual-subtype injectivity;
- parent-relative `terminalNeighborCode` equality;
- treating deleted `X` as a residual terminal neighbor for
  `residual = X.erase deleted`;
- the v2.161 selector-image circular chain.

## Validation

This is a dashboard-only scope artifact.  No Lean file was edited, so no
`lake build` was required for this task.

The artifact names the exact bridge into
`PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealization1296`
and isolates residual-value code separation rather than selected-image
cardinality, bounded menu cardinality, local codes, parent-relative selector
codes, empirical search, `finsetCodeOfCardLe`, deleted-X shortcuts, or the
v2.161 cycle.

F3-COUNT remains `CONDITIONAL_BRIDGE`; no status, percentage, README metric,
planner metric, ledger row, proof claim, or Clay-level claim moved.

## Next Task

```text
CODEX-F3-BASE-ZONE-RESIDUAL-VALUE-CODE-SEPARATION-INTERFACE-001
```

Add the no-sorry Lean Prop/interface
`PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSeparation1296`
and, only if it builds without `sorry`, prove the erasure bridge
`physicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealization1296_of_baseZoneResidualValueCodeSeparation1296`.
