# F3 residual bookkeeping tag space injection scope v2.212

Task: `CODEX-F3-BOOKKEEPING-TAG-SPACE-INJECTION-SCOPE-001`

Status: `DONE_SCOPE_DELIVERED_NO_LEAN_NO_STATUS_MOVE`

## Proposed theorem

Tentative Lean target:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagSpaceInjection1296
```

This should be the structural source upstream of:

```lean
PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBookkeepingTagInjection1296
```

The target is not a proof of F3-COUNT.  It isolates the residual bookkeeping/base-zone tag structure that v2.211 found missing: a tag space must exist before any fixed terminal-neighbor selector, selected image, or bounded menu is supplied, and it must separate selector-admissible residual values.

## Required shape

Under the same v2.121 bookkeeping residual-fiber hypotheses used by `PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBookkeepingTagInjection1296`, the theorem should expose a package equivalent to:

```lean
exists bookkeepingTagSpace : forall residual, Type,
exists bookkeepingTagOfResidualVertex :
  forall residual,
    {q : ConcretePlaquette physicalClayDimension L // q in residual} ->
      bookkeepingTagSpace residual,
exists bookkeepingTagIntoFin1296 :
  forall residual, bookkeepingTagSpace residual -> Fin 1296,
...
```

The package must include a selected-admissible tag-injectivity law:

```lean
forall residual
  (a b : {q : ConcretePlaquette physicalClayDimension L // q in residual}),
  (exists p : {p : ConcretePlaquette physicalClayDimension L //
      p in essential residual},
    Nonempty
      (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
        residual p.1 a)) ->
  (exists p : {p : ConcretePlaquette physicalClayDimension L //
      p in essential residual},
    Nonempty
      (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
        residual p.1 b)) ->
  bookkeepingTagIntoFin1296 residual
      (bookkeepingTagOfResidualVertex residual a) =
    bookkeepingTagIntoFin1296 residual
      (bookkeepingTagOfResidualVertex residual b) ->
  a.1 = b.1
```

The tag space can be implemented as a concrete finite bookkeeping/base-zone type, an indexed base-zone enumeration, or a proof-relevant structural coordinate, but the code must be defined on residual values before a selected terminal-neighbor image or menu is known.

## Exact bridge

Expected bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBookkeepingTagInjection1296
```

Expected bridge name:

```lean
physicalPlaquetteGraphResidualFiberSelectorAdmissibleBookkeepingTagInjection1296_of_residualFiberBookkeepingTagSpaceInjection1296
```

The bridge should be a repackaging:

1. apply the tag-space injection theorem to the v2.121 bookkeeping hypotheses;
2. define `PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCodeData residual` by composing `bookkeepingTagOfResidualVertex residual` with `bookkeepingTagIntoFin1296 residual`;
3. pass selector-admissibility witnesses and equal `Fin 1296` codes to the tag-injectivity law;
4. return equality of residual values.

No selected-image cardinality, bounded menu, empirical search, `finsetCodeOfCardLe`, root-shell/local-neighbor/local-displacement code, parent-relative `terminalNeighborCode`, deleted-X residual shortcut, or v2.161 cycle should appear in the bridge.

## Candidate implementation routes

The scope permits three non-circular structural presentations:

- `baseZoneTagSpace`: define a residual bookkeeping/base-zone type and a tag extractor for residual vertices, then prove selector-admissible tag injectivity.
- `ambientCoordinateTagSpace`: define a selector-independent ambient coordinate for each residual vertex and an injection of admissible coordinate values into `Fin 1296`.
- `proofRelevantAdmissibleTag`: define a proof-relevant tag relation whose code is residual-value based and whose injectivity is stated only for values carrying selector-data evidence.

All routes must define tags on the residual subtype itself, not on an already selected image or bounded menu.

## Distinctions from rejected routes

This scope does not use or authorize:

- selected-image cardinality;
- bounded menu cardinality;
- empirical search;
- `finsetCodeOfCardLe`;
- the v2.161 selector-image cycle;
- root-shell codes as residual-subtype bookkeeping tag injectivity;
- local-neighbor codes as residual-subtype bookkeeping tag injectivity;
- local-displacement codes as residual-subtype bookkeeping tag injectivity;
- parent-relative `terminalNeighborCode` equality;
- treating deleted `X` as a residual terminal neighbor for `residual = X.erase (deleted X)`.

`PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCodeData` remains the downstream code-data shape, not the structural proof source: it has a `bookkeepingTagCode` field but does not explain the tag space, extractor, injection, or selected-admissible injectivity.

## Validation

Dashboard-only scope.  No Lean file was edited, so no `lake build` is required for this task.

The artifact names the exact bridge into `PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBookkeepingTagInjection1296` and keeps residual bookkeeping tag space injection distinct from selected-image, bounded-menu, empirical, `finsetCodeOfCardLe`, root-shell/local-neighbor/local-displacement, parent-relative `terminalNeighborCode`, deleted-X residual, and v2.161-cycle routes.

F3-COUNT remains `CONDITIONAL_BRIDGE`. No status, percentage, README metric, planner metric, ledger row, vacuity caveat, proof claim, or Clay-level claim moved.

## Next task

`CODEX-F3-BOOKKEEPING-TAG-SPACE-INJECTION-INTERFACE-001`

Add a no-sorry Lean Prop/interface for `PhysicalPlaquetteGraphResidualFiberBookkeepingTagSpaceInjection1296` and, only if it builds without sorry, the bridge into `PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBookkeepingTagInjection1296`.
