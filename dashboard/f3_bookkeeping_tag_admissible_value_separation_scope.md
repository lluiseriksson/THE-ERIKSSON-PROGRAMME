# F3 bookkeeping tag admissible-value separation scope v2.206

Task: `CODEX-F3-BOOKKEEPING-TAG-ADMISSIBLE-VALUE-SEPARATION-SCOPE-001`

## Proposed theorem

Tentative Lean target:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagAdmissibleValueSeparation1296
```

This should be the structural source upstream of:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagCoordinate1296
```

The theorem is not a proof of F3-COUNT.  It isolates the exact separation
burden left by v2.205: a bookkeeping/base-zone coordinate chosen on each
residual subtype before any selector is fixed must separate every residual
value that is admissible as a terminal-neighbor value under
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` evidence.

## Required shape

Under the v2.121 bookkeeping residual-fiber hypotheses, the theorem should
produce residual-indexed bookkeeping tag data:

```lean
exists bookkeepingTagCodeData :
  forall residual,
    PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCodeData
      residual,
...
```

The separation clause should quantify over residual values directly, not over
an already formed selected image:

```lean
forall residual
  (a b : {q : ConcretePlaquette physicalClayDimension L // q in residual}),
  (exists p : {p : ConcretePlaquette physicalClayDimension L //
      p in essential residual},
    PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
      residual p.1 a) ->
  (exists p : {p : ConcretePlaquette physicalClayDimension L //
      p in essential residual},
    PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
      residual p.1 b) ->
  (bookkeepingTagCodeData residual).bookkeepingTagCode a =
    (bookkeepingTagCodeData residual).bookkeepingTagCode b ->
  a.1 = b.1
```

This is intentionally stronger than v2.204's coordinate theorem in one
specific way: it proves separation on the whole selector-admissible value
relation for the residual, before a concrete `terminalNeighborOfParent`
function is supplied.  It is still narrower than full injectivity of the whole
residual subtype into `Fin 1296`, because it only separates values that carry
terminal-neighbor selector evidence from an essential parent.

## Exact bridge

Expected bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagCoordinate1296
```

Expected bridge name:

```lean
physicalPlaquetteGraphResidualFiberBookkeepingTagCoordinate1296_of_residualFiberBookkeepingTagAdmissibleValueSeparation1296
```

The bridge should be direct:

1. apply the admissible-value separation theorem to the v2.121 bookkeeping
   hypotheses;
2. obtain the residual-indexed `bookkeepingTagCodeData`;
3. after the caller supplies a fixed `terminalNeighborOfParent` and selector
   evidence, prove each selected value is selector-admissible using the
   corresponding essential parent and evidence;
4. pass the code equality through the admissible-value separation clause.

## Distinctions from rejected routes

This scope does not use or authorize:

- selected-image cardinality;
- bounded menu cardinality;
- empirical search;
- `finsetCodeOfCardLe`;
- the v2.161 selector-image cycle;
- root-shell codes as residual-subtype bookkeeping tag injectivity;
- local neighbor codes as residual-subtype bookkeeping tag injectivity;
- local displacement codes as residual-subtype bookkeeping tag injectivity;
- parent-relative `terminalNeighborCode` equality;
- treating deleted `X` as a residual terminal neighbor for
  `residual = X.erase (deleted X)`.

The key distinction is source order.  Selected-image coding begins after a
selector is fixed; this theorem must provide a coordinate and separation law
before the selector is supplied.  Root-shell and local codes may remain useful
for naming context, but they do not prove this admissible residual-value
separation law.

## Validation

Dashboard-only scope.  No Lean file was edited, so no `lake build` is required
for this task.

The artifact names the exact bridge into
`PhysicalPlaquetteGraphResidualFiberBookkeepingTagCoordinate1296` and keeps
selector-admissible residual-value separation distinct from selected-image,
bounded-menu, empirical, `finsetCodeOfCardLe`, root-shell/local-neighbor/local
displacement, parent-relative `terminalNeighborCode`, deleted-X residual, and
v2.161-cycle routes.

F3-COUNT remains `CONDITIONAL_BRIDGE`. No status, percentage, README metric,
planner metric, ledger row, vacuity caveat, proof claim, or Clay-level claim
moved.

## Next task

`CODEX-F3-BOOKKEEPING-TAG-ADMISSIBLE-VALUE-SEPARATION-INTERFACE-001`

Add a no-sorry Lean Prop/interface for
`PhysicalPlaquetteGraphResidualFiberBookkeepingTagAdmissibleValueSeparation1296`
and, only if it builds without sorry, the bridge into
`PhysicalPlaquetteGraphResidualFiberBookkeepingTagCoordinate1296`.
