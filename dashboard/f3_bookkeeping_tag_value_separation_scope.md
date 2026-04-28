# F3 bookkeeping tag value-separation scope v2.200

Task: `CODEX-F3-BOOKKEEPING-TAG-VALUE-SEPARATION-SCOPE-001`

## Proposed theorem

Tentative Lean target:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueSeparation1296
```

This should be the structural source theorem upstream of:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueCodeSource1296
```

The goal is not to close F3-COUNT.  It is to isolate the exact residual-value
bookkeeping/base-zone separation burden that v2.199 identified as missing.

## Required shape

Under the v2.121 bookkeeping residual-fiber hypotheses, for a fixed
residual-local selector

```lean
terminalNeighborOfParent :
  forall residual,
    (p : {p : ConcretePlaquette physicalClayDimension L //
      p in essential residual}) ->
      {q : ConcretePlaquette physicalClayDimension L // q in residual}
```

and selector evidence

```lean
forall residual p,
  PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
    residual p (terminalNeighborOfParent residual p)
```

the theorem must provide residual-value bookkeeping tag data

```lean
forall residual,
  PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCodeData
    residual
```

and selected-value separation for the fixed selector:

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

The code is required on the whole residual subtype before restricting to
selected terminal-neighbor values.  The selected-value separation is a
structural property of that residual-value bookkeeping tag, not a code
manufactured from the selected image.

## Bridge to value-code source

Expected bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueCodeSource1296
```

Expected bridge name:

```lean
physicalPlaquetteGraphResidualFiberBookkeepingTagValueCodeSource1296_of_residualFiberBookkeepingTagValueSeparation1296
```

The bridge should be pure repacking: from the value-separation source, provide
the `bookkeepingTagCodeData` family and the selected-value separation required
by `PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueCodeSource1296`.

## Candidate structural burden

The next Lean interface should expose the structural gap without pretending it
is already solved:

- identify a bookkeeping/base-zone tag source defined on every residual value;
- prove equality of those tags separates the values selected by a fixed
  `terminalNeighborOfParent`;
- keep this source independent of the selected image and independent of the
  per-parent selector code stored inside selector evidence.

Existing ingredients remain insufficient:

- root-shell codes code first-shell elements of an anchored bucket, not
  arbitrary residual subtype values;
- local neighbor or displacement codes are parent-relative/local, not a
  residual-subtype bookkeeping tag;
- `terminalNeighborCode : Fin 1296` inside
  `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` is
  per-parent selector evidence and cannot be used as residual tag injectivity.

## Explicit non-routes

This scope does not use or authorize:

- selected-image cardinality;
- bounded menu cardinality;
- empirical search;
- `finsetCodeOfCardLe`;
- the v2.161 selector-image cycle;
- local displacement codes;
- root-shell codes as residual-subtype tag injectivity;
- local neighbor codes as residual-subtype tag injectivity;
- parent-relative `terminalNeighborCode` equality;
- treating deleted `X` as a residual terminal neighbor for
  `residual = X.erase (deleted X)`.

## Validation

Dashboard-only scope.  No Lean file was edited, so no lake build is required
for this task.  The artifact names the exact bridge into
`PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueCodeSource1296` and
keeps residual-value bookkeeping separation distinct from root-shell, local
neighbor, selected-image, bounded-menu, empirical, `finsetCodeOfCardLe`, and
v2.161-cycle routes.

F3-COUNT remains `CONDITIONAL_BRIDGE`. No status, percentage, README metric,
planner metric, ledger row, vacuity caveat, proof claim, or Clay-level claim
moved.

## Next task

`CODEX-F3-BOOKKEEPING-TAG-VALUE-SEPARATION-INTERFACE-001`

Add a no-sorry Lean Prop/interface for
`PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueSeparation1296` and, only
if it builds without sorry, the bridge into
`PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueCodeSource1296`.
