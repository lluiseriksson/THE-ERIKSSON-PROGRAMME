# F3 residual bookkeeping tag coordinate scope v2.203

Task: `CODEX-F3-RESIDUAL-BOOKKEEPING-TAG-COORDINATE-SCOPE-001`

## Proposed theorem

Tentative Lean target:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagCoordinate1296
```

This should be the structural coordinate source upstream of:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueSeparation1296
```

The theorem is not a proof of F3-COUNT.  It isolates the coordinate burden
left by v2.202: a residual bookkeeping/base-zone `Fin 1296` tag must be chosen
on the whole residual subtype before any selected terminal-neighbor image is
formed.

## Required shape

Under the v2.121 bookkeeping residual-fiber hypotheses, the theorem should
produce residual-value bookkeeping tag data first:

```lean
exists bookkeepingTagCodeData :
  forall residual,
    PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCodeData
      residual,
...
```

The code family is structural for each residual fiber.  It must not depend on a
particular finite selected image, menu, empirical list, or post-hoc current
witness.

Only after the coordinate data has been supplied should the theorem quantify
over a fixed residual-local selector:

```lean
terminalNeighborOfParent :
  forall residual,
    (p : {p : ConcretePlaquette physicalClayDimension L //
      p in essential residual}) ->
      {q : ConcretePlaquette physicalClayDimension L // q in residual}
```

and selector evidence:

```lean
forall residual p,
  PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
    residual p.1 (terminalNeighborOfParent residual p)
```

The separation clause should then restrict the structural coordinate to the
selected values:

```lean
forall residual
  (p q : {p : ConcretePlaquette physicalClayDimension L //
    p in essential residual}),
  (bookkeepingTagCodeData residual).bookkeepingTagCode
      (terminalNeighborOfParent residual p) =
    (bookkeepingTagCodeData residual).bookkeepingTagCode
      (terminalNeighborOfParent residual q) ->
    (terminalNeighborOfParent residual p).1 =
      (terminalNeighborOfParent residual q).1
```

This is intentionally stronger in source order than
`PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueSeparation1296`: the
coordinate is produced before the selector/evidence arguments, so the bridge
cannot manufacture a code from the selected terminal-neighbor image.

## Exact bridge

Expected bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueSeparation1296
```

Expected bridge name:

```lean
physicalPlaquetteGraphResidualFiberBookkeepingTagValueSeparation1296_of_residualFiberBookkeepingTagCoordinate1296
```

The bridge should be direct repackaging:

1. apply the coordinate theorem to the v2.121 bookkeeping hypotheses;
2. obtain the residual-indexed `bookkeepingTagCodeData`;
3. after the caller supplies `terminalNeighborOfParent` and selector evidence,
   pass through the coordinate separation clause for selected values.

## Distinctions from rejected routes

This scope does not use or authorize:

- selected-image cardinality;
- bounded menu cardinality;
- empirical search;
- `finsetCodeOfCardLe`;
- the v2.161 selector-image cycle;
- root-shell codes as residual-subtype tag injectivity;
- local neighbor codes as residual-subtype tag injectivity;
- local displacement codes;
- parent-relative `terminalNeighborCode` equality;
- treating deleted `X` as a residual terminal neighbor for
  `residual = X.erase (deleted X)`.

The root-shell and local-neighbor APIs can remain useful naming context, but
they do not supply this theorem: they code first-shell or local/root-relative
objects, not a bookkeeping/base-zone coordinate on every value of an arbitrary
v2.121 residual subtype.

## Validation

Dashboard-only scope.  No Lean file was edited, so no `lake build` is required
for this task.

The artifact names the exact bridge into
`PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueSeparation1296` and
keeps residual bookkeeping/base-zone coordinates distinct from root-shell,
local-neighbor, selected-image, bounded-menu, empirical,
`finsetCodeOfCardLe`, and v2.161-cycle routes.

F3-COUNT remains `CONDITIONAL_BRIDGE`. No status, percentage, README metric,
planner metric, ledger row, vacuity caveat, proof claim, or Clay-level claim
moved.

## Next task

`CODEX-F3-RESIDUAL-BOOKKEEPING-TAG-COORDINATE-INTERFACE-001`

Add a no-sorry Lean Prop/interface for
`PhysicalPlaquetteGraphResidualFiberBookkeepingTagCoordinate1296` and, only if
it builds without sorry, the bridge into
`PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueSeparation1296`.
