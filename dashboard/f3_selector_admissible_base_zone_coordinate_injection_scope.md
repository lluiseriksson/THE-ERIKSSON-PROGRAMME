# F3 selector-admissible base-zone coordinate injection scope

Task: `CODEX-F3-SELECTOR-ADMISSIBLE-BASE-ZONE-COORDINATE-INJECTION-SCOPE-001`

Status: `DONE_SCOPE_DELIVERED_NO_LEAN_NO_STATUS_MOVE`

Date: 2026-04-28T00:05:59Z

## Proposed upstream theorem

Tentative Lean target:

```lean
PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296
```

This theorem should be the structural source below the v2.218 coordinate
interface:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296
```

It must isolate a selector-independent residual bookkeeping/base-zone coordinate
on the whole residual subtype, an encoding into `Fin 1296`, and
selected-admissible injectivity for residual values carrying
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` evidence from
essential parents.

## Exact bridge

Bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296
```

Expected bridge name:

```lean
physicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296_of_residualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296
```

Bridge shape:

1. assume
   `PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296`;
2. under the v2.121 bookkeeping residual-fiber hypotheses, obtain the
   selector-independent coordinate package;
3. instantiate
   `PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinateData`
   with the package's residual coordinate space, residual-value extractor, and
   `Fin 1296` encoder;
4. project the source theorem's selected-admissible injectivity law into the
   `selectedAdmissible_injective` field;
5. return
   `PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296`.

This bridge should be definitional/structural repackaging only.

## Required source payload

The upstream theorem should provide, for each residual fiber produced by the
v2.121 bookkeeping hypotheses:

```lean
baseZoneCoordinateSpace :
  Finset (ConcretePlaquette physicalClayDimension L) -> Type

baseZoneCoordinateOfResidualValue :
  forall residual,
    {q : ConcretePlaquette physicalClayDimension L // q in residual} ->
      baseZoneCoordinateSpace residual

baseZoneCoordinateCode :
  forall residual, baseZoneCoordinateSpace residual -> Fin 1296
```

and the selected-admissible injectivity law:

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
  baseZoneCoordinateCode residual
      (baseZoneCoordinateOfResidualValue residual a) =
    baseZoneCoordinateCode residual
      (baseZoneCoordinateOfResidualValue residual b) ->
  a.1 = b.1
```

The coordinate space and extractor must be defined before any fixed
`terminalNeighborOfParent` selector, selected image, or bounded menu is supplied.
Only the injectivity law may restrict to selector-admissible residual values.

## Non-circular formulations

### Route A: primitive base-zone coordinate relation

Introduce a proof-relevant base-zone coordinate relation on residual values and
prove that selector-admissible values have unique relation witnesses.  The
`Fin 1296` encoder is then attached to coordinate witnesses, not to a selected
image.  The blocker is a structural uniqueness theorem for the relation under
v2.121 bookkeeping.

### Route B: residual bookkeeping coordinate extractor

Extract a residual bookkeeping/base-zone coordinate directly from the
`parentOf`/`essential` bookkeeping data and prove that selector-admissible
terminal-neighbor values with equal coordinates are equal.  This is the most
direct intended route, but it needs a theorem showing that the v2.121
bookkeeping carries coordinate information about residual values, not only
essential-parent membership and residual subset facts.

### Route C: ambient base-zone coordinate restricted by admissibility

Define a selector-independent ambient/base-zone coordinate for every residual
value, encode it into `Fin 1296`, and prove an admissibility theorem saying
that selector-data evidence forces equality of residual values when the
coordinate codes agree.  This route is valid only if the coordinate is a true
bookkeeping/base-zone coordinate, not a root-shell, local-neighbor,
local-displacement, or parent-relative terminal-neighbor code.

## Distinctions from existing artifacts

- `PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296` is
  the v2.218 downstream interface to be supplied; it does not itself explain
  the structural source of the coordinate.
- `PhysicalPlaquetteGraphResidualFiberBookkeepingTagSpaceInjection1296` is still
  farther downstream and should be reached through the v2.218 bridge, not used
  as the source theorem here.
- `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` supplies
  admissibility evidence for selected residual values, but its
  `terminalNeighborCode` is parent-relative and cannot be used as residual
  bookkeeping tag injectivity.
- Root-shell, local-neighbor, and local-displacement codes are not whole
  residual-subtype bookkeeping/base-zone coordinates.

## Rejected routes

This scope does not use or authorize:

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

- This dashboard scope note exists.
- The artifact names the exact bridge into
  `PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296`.
- No Lean file was edited; no `lake build` was required for this dashboard-only
  scope.
- F3-COUNT remains `CONDITIONAL_BRIDGE`; no status, percentage, README metric,
  planner metric, ledger row, proof claim, or Clay-level claim moved.

## Next task

```text
CODEX-F3-SELECTOR-ADMISSIBLE-BASE-ZONE-COORDINATE-INJECTION-INTERFACE-001
```

Add a no-sorry Lean Prop/interface for
`PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296`
and, only if it builds without `sorry`, the bridge
`physicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296_of_residualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296`.
