# F3 bookkeeping base-zone tag coordinate scope recovery

Task: `CODEX-F3-BOOKKEEPING-BASE-ZONE-TAG-COORDINATE-SCOPE-RECOVERY-001`  
Status: `DONE_SCOPE_RECOVERED_NO_PRIOR_COMPLETION_EVIDENCE`  
Date: 2026-04-27T23:35:42Z

## Recovery check

The prior task
`CODEX-F3-BOOKKEEPING-BASE-ZONE-TAG-COORDINATE-SCOPE-001` was still marked
`IN_PROGRESS`, but the repository search found no completion artifact named
for `base_zone_tag_coordinate`, and the current Lean file contains no
`PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296`
definition.  No conflicting completion evidence was found.

This note therefore supersedes that stale in-progress scope lane without
claiming that the stale task itself completed a mathematical deliverable.

## Proposed upstream theorem

Tentative Lean target:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296
```

The theorem should be a structural source below:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagSpaceInjection1296
```

It must construct a selector-independent residual bookkeeping/base-zone
coordinate before any selected terminal-neighbor image, bounded menu, or fixed
selector-derived code is supplied.

## Exact bridge

Proposed bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagSpaceInjection1296
```

Proposed bridge name:

```lean
physicalPlaquetteGraphResidualFiberBookkeepingTagSpaceInjection1296_of_residualFiberBookkeepingBaseZoneTagCoordinate1296
```

Bridge shape:

1. apply the base-zone coordinate source under the v2.121 bookkeeping
   residual-fiber hypotheses;
2. instantiate the `bookkeepingTagSpace`, residual-value tag extractor, and
   `Fin 1296` encoding required by
   `PhysicalPlaquetteGraphResidualFiberBookkeepingTagSpaceInjection1296`;
3. use the source theorem's selected-admissible coordinate injectivity for
   residual values carrying
   `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` evidence
   from essential parents;
4. return the tag-space injection package without using selected-image
   cardinality or menu cardinality.

## Required coordinate payload

The source theorem should expose a package equivalent to:

```lean
exists baseZoneTagSpace :
  forall residual, Type
exists baseZoneTagOfResidualValue :
  forall residual,
    {q : ConcretePlaquette physicalClayDimension L // q in residual} ->
      baseZoneTagSpace residual
exists baseZoneTagCode :
  forall residual, baseZoneTagSpace residual -> Fin 1296
```

and a selected-admissible separation law:

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
  baseZoneTagCode residual (baseZoneTagOfResidualValue residual a) =
    baseZoneTagCode residual (baseZoneTagOfResidualValue residual b) ->
  a.1 = b.1
```

The coordinate must be defined on the whole residual subtype.  The
selector-admissibility hypotheses may restrict where injectivity is required,
but they must not define the coordinate by packing a selected image.

## Candidate non-circular formulations

### Route A: residual base-zone coordinate source

Define a bookkeeping/base-zone coordinate space for each residual fiber from
the v2.121 bookkeeping data, then prove that selector-admissible terminal
neighbor values have unique coordinates.  This is the cleanest intended source,
but it currently needs a new structural lemma explaining why the v2.121
`essential = image parentOf` bookkeeping carries a residual-value coordinate
rather than only parent membership/subset data.

### Route B: ambient coordinate with base-zone admissibility law

Define a selector-independent ambient coordinate on residual values and an
encoding into `Fin 1296`, then prove a base-zone admissibility theorem saying
that two selector-admissible residual values with equal coordinate are equal.
This route is acceptable only if the coordinate is a residual bookkeeping/base
coordinate, not a root-shell, local-neighbor, local-displacement, or
parent-relative `terminalNeighborCode` surrogate.

### Route C: proof-relevant base-zone certificate

Use a proof-relevant tag relation or certificate attached to residual values,
with a `Fin 1296` encoding and an injectivity theorem for values admitting
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`.  This route
keeps the coordinate source separate from selected-image cardinality, but its
blocker is to prove certificate uniqueness without deriving it from a selected
image or bounded menu.

## Distinctions from existing artifacts

- `PhysicalPlaquetteGraphResidualFiberBookkeepingTagSpaceInjection1296` is the
  downstream tag-space interface.  The new coordinate theorem must be a source
  that supplies its tag space and injectivity law.
- `PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCodeData`
  is only a code-data carrier.  It does not explain the tag source or prove
  selected-admissible separation.
- `PhysicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296` supplies
  deleted/parent/essential/residual-subset bookkeeping, but no residual
  coordinate extractor or admissible-value injectivity law.
- `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` supplies
  admissibility evidence and a parent-relative `terminalNeighborCode`; that code
  is not the residual bookkeeping/base-zone coordinate.

## Rejected routes

This recovery scope does not use or authorize:

- selected-image cardinality;
- bounded menu cardinality;
- empirical search;
- `finsetCodeOfCardLe`;
- root-shell codes as residual-subtype bookkeeping tag injectivity;
- local-neighbor codes as residual-subtype bookkeeping tag injectivity;
- local-displacement codes as residual-subtype bookkeeping tag injectivity;
- parent-relative `terminalNeighborCode` equality;
- treating deleted `X` as a residual terminal neighbor for
  `residual = X.erase (deleted X)`;
- the v2.161 selector-image cycle.

## Validation

- This dashboard note exists and supersedes the stale prior scope lane because
  no completion evidence was found.
- The artifact names the exact bridge into
  `PhysicalPlaquetteGraphResidualFiberBookkeepingTagSpaceInjection1296`.
- F3-COUNT remains `CONDITIONAL_BRIDGE`; no status, percentage, README metric,
  planner metric, ledger row, proof claim, or Clay-level claim moved.

## Next task

```text
CODEX-F3-BOOKKEEPING-BASE-ZONE-TAG-COORDINATE-INTERFACE-001
```

Add a no-sorry Lean Prop/interface for
`PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296` and,
only if it builds without `sorry`, the bridge
`physicalPlaquetteGraphResidualFiberBookkeepingTagSpaceInjection1296_of_residualFiberBookkeepingBaseZoneTagCoordinate1296`.
