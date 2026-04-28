# F3 base-zone coordinate candidate-lemma inventory

Task: `CODEX-F3-BASE-ZONE-COORDINATE-CANDIDATE-LEMMA-INVENTORY-001`

Status: `DONE_INVENTORY_EXACT_BLOCKER_COORDINATE_SOURCE_MISSING`

Date: 2026-04-28T00:55:00Z

## Scope

This inventory checks the current Lean surface that could support:

```lean
PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296
```

or the existing bridge into:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296
```

No Lean theorem was added.  No F3 status, percentage, README metric, planner
metric, ledger row, proof claim, or Clay-level claim moved.

## Candidate map

### Current interface and bridge

- `PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjectionData`
  (`YangMills/ClayCore/LatticeAnimalCount.lean:3999`) is the exact carrier
  required by the v2.220 source interface: coordinate space, residual-value
  extractor, `Fin 1296` encoder, and selected-admissible injectivity.
- `PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296`
  (`YangMills/ClayCore/LatticeAnimalCount.lean:4226`) is the immediate target
  needing a proof.  It is an interface, not a construction.
- `physicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296_of_residualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296`
  (`YangMills/ClayCore/LatticeAnimalCount.lean:4407`) is the exact structural
  bridge into
  `PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296`.
  It is usable once the source theorem exists.

### Downstream carriers

- `PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinateData`
  (`YangMills/ClayCore/LatticeAnimalCount.lean:3955`) names the downstream
  base-zone tag payload but does not construct it.
- `PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296`
  (`YangMills/ClayCore/LatticeAnimalCount.lean:4149`) is the downstream
  coordinate interface supplied by the v2.220 bridge.
- `PhysicalPlaquetteGraphResidualFiberBookkeepingTagSpaceInjection1296`
  (`YangMills/ClayCore/LatticeAnimalCount.lean:4275`) is farther downstream:
  it consumes a residual bookkeeping/base-zone tag source, so it cannot serve
  as the missing source for the current target.

### Admissibility evidence

- `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`
  (`YangMills/ClayCore/LatticeAnimalCount.lean:3413`) is the correct
  admissibility witness carried by selected residual values.  Its
  `terminalNeighborCode` field is parent-relative and is not a residual
  bookkeeping/base-zone coordinate.
- `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296`
  (`YangMills/ClayCore/LatticeAnimalCount.lean:5943`) and theorem
  `physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296`
  (`YangMills/ClayCore/LatticeAnimalCount.lean:6030`) can supply selector-data
  witnesses.  They still do not define a selector-independent coordinate space,
  residual-value extractor, or `Fin 1296` injection.

### Bookkeeping context

- The v2.121 bookkeeping hypotheses, as reused by the interfaces above, provide
  residual fibers, deleted/parent data, `essential residual`, and
  `essential residual ⊆ residual`.  These are necessary context for a future
  source theorem, but the current Lean API does not expose a residual
  base-zone coordinate extractor from them.
- The v2.219 attempt already records that using the residual subtype itself as
  the tag space would require an unavailable injection of residual values into
  `Fin 1296`.

## Rejected non-candidates

- `finsetCodeOfCardLe` and `finsetCodeOfCardLe_injective`
  (`YangMills/ClayCore/LatticeAnimalCount.lean:438`, `:443`) are not valid
  here; they would manufacture a code from bounded cardinality rather than a
  structural base-zone coordinate source.
- `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellCode1296_injective`
  (`YangMills/ClayCore/LatticeAnimalCount.lean:1547`) proves injectivity only
  for first-shell/root-shell values, not whole residual-subtype base-zone
  coordinates.
- `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_rootShellCode1296_reachable_to_member`
  (`YangMills/ClayCore/LatticeAnimalCount.lean:8302`) and
  `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParentCode1296_spec`
  (`YangMills/ClayCore/LatticeAnimalCount.lean:8376`) provide root-shell
  reachability/code stability, not selected-admissible residual-value
  separation.
- `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_root_neighborCode1296`
  (`YangMills/ClayCore/LatticeAnimalCount.lean:8410`) is a local/root-neighbor
  code and cannot be treated as residual-subtype bookkeeping/base-zone
  injectivity.
- Selected-image cardinality, bounded menu cardinality, empirical search,
  parent-relative `terminalNeighborCode` equality, root-shell/local-neighbor/
  local-displacement codes, deleted-X shortcuts, and the v2.161 selector-image
  cycle remain non-routes.

## Exact blocker

No existing Lean lemma currently supplies the selector-independent base-zone
coordinate source needed to prove
`PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296`.

The exact next source to scope is:

```lean
PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296
```

It should provide, under the v2.121 bookkeeping residual-fiber hypotheses:

1. a residual bookkeeping/base-zone coordinate space on the whole residual
   subtype;
2. a residual-value coordinate extractor defined before any selected image,
   bounded menu, or fixed selector is supplied;
3. an encoding into `Fin 1296`;
4. selected-admissible injectivity for residual values carrying
   `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` evidence
   from essential parents.

The intended bridge target is:

```lean
PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296
```

## Validation

- Dashboard note records the candidate-lemma map and exact blocker.
- No Lean file was edited.
- YAML/JSON/JSONL validation is required after registry updates.
- F3-COUNT remains `CONDITIONAL_BRIDGE`; no percentage moved.
