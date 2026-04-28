# F3 selector-admissible bookkeeping tag injection scope v2.209

Task: `CODEX-F3-SELECTOR-ADMISSIBLE-BOOKKEEPING-TAG-INJECTION-SCOPE-001`

## Proposed theorem

Tentative Lean target:

```lean
PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBookkeepingTagInjection1296
```

This should be the structural source upstream of:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagAdmissibleValueSeparation1296
```

The target is not a proof of F3-COUNT.  It isolates the exact bookkeeping-tag
burden left by v2.208: a residual-value tag code must be chosen before any
selected image or bounded menu is formed, and equal tags must separate every
residual value that is admissible through
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` evidence from
an essential parent.

## Required shape

Under the same v2.121 bookkeeping residual-fiber hypotheses used by
`PhysicalPlaquetteGraphResidualFiberBookkeepingTagAdmissibleValueSeparation1296`,
the theorem should expose a structural package equivalent to:

```lean
exists bookkeepingTagCodeData :
  forall residual,
    PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCodeData
      residual,
...
```

The data should be read as a residual bookkeeping/base-zone tag package:

- a residual-value tag extractor;
- an ambient or bookkeeping tag space independent of a fixed selector;
- an injection of that tag space into `Fin 1296`, or an equivalent
  `PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCodeData`
  field;
- a selector-admissible separation law.

The separation law should quantify over residual subtype values directly:

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
  (bookkeepingTagCodeData residual).bookkeepingTagCode a =
    (bookkeepingTagCodeData residual).bookkeepingTagCode b ->
  a.1 = b.1
```

This is narrower than full injectivity of the entire residual subtype only if
the implementation chooses a proof-relevant admissible subrelation.  It is
stronger than a per-parent code because the code is attached to residual
values before the selected terminal-neighbor function is fixed.

## Exact bridge

Expected bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagAdmissibleValueSeparation1296
```

Expected bridge name:

```lean
physicalPlaquetteGraphResidualFiberBookkeepingTagAdmissibleValueSeparation1296_of_residualFiberSelectorAdmissibleBookkeepingTagInjection1296
```

The bridge should be direct:

1. apply the selector-admissible bookkeeping-tag injection theorem to the
   v2.121 bookkeeping hypotheses;
2. obtain the residual-indexed `bookkeepingTagCodeData`;
3. pass the two selector-admissibility witnesses and code equality to the
   injection/separation clause;
4. return the resulting residual value equality.

No selected image, bounded menu, or `finsetCodeOfCardLe` construction should
appear in the bridge.

## Candidate implementation routes

The scope permits three equivalent structural presentations, in descending
preference:

1. `bookkeepingTag` route: formalize a residual-value `BookkeepingTagSpace`,
   `bookkeepingTagOfResidualVertex`, and `bookkeepingTagIntoFin1296`, then prove
   selector-admissible values with equal bookkeeping tags are equal.
2. `baseZoneEnumeration` route: formalize the ambient base-zone enumeration
   and prove every selector-admissible residual value maps into that base zone
   with injective `Fin 1296` index.
3. `canonicalLastEdgeFrontier` route: factor the residual value through a
   selector-independent canonical-last-edge/frontier coordinate pair and a
   structural pairing into `Fin 1296`.

All three routes must define the code before a selected terminal-neighbor image
or bounded menu is known.

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

Root-shell, local-neighbor, and parent-relative codes may appear in the
inventory only as rejected evidence or as non-load-bearing context.  They do
not supply residual bookkeeping tag injectivity.

## Validation

Dashboard-only scope.  No Lean file was edited, so no `lake build` is required
for this task.

The artifact names the exact bridge into
`PhysicalPlaquetteGraphResidualFiberBookkeepingTagAdmissibleValueSeparation1296`
and keeps selector-admissible bookkeeping tags distinct from selected-image,
bounded-menu, empirical, `finsetCodeOfCardLe`, root-shell/local-neighbor/local
displacement, parent-relative `terminalNeighborCode`, deleted-X residual, and
v2.161-cycle routes.

F3-COUNT remains `CONDITIONAL_BRIDGE`. No status, percentage, README metric,
planner metric, ledger row, vacuity caveat, proof claim, or Clay-level claim
moved.

## Next task

`CODEX-F3-SELECTOR-ADMISSIBLE-BOOKKEEPING-TAG-INJECTION-INTERFACE-001`

Add a no-sorry Lean Prop/interface for
`PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBookkeepingTagInjection1296`
and, only if it builds without sorry, the bridge into
`PhysicalPlaquetteGraphResidualFiberBookkeepingTagAdmissibleValueSeparation1296`.
