# F3 admissible-value separation candidate-lemma inventory

Task: `CODEX-F3-ADMISSIBLE-VALUE-SEPARATION-CANDIDATE-LEMMA-INVENTORY-001`  
Status: `DONE_INVENTORY_EXACT_BLOCKER_BASE_ZONE_TAG_COORDINATE_MISSING`  
Date: 2026-04-27T23:21:01Z

## Scope

This inventory checks the current Lean surface that could support either:

- `PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBookkeepingTagInjection1296`, or
- the bridge into `PhysicalPlaquetteGraphResidualFiberBookkeepingTagAdmissibleValueSeparation1296`.

It is dashboard-only.  No Lean theorem, F3 status, percentage, README metric,
planner metric, ledger row, or Clay-level claim moved.

## Candidate map

### Immediate Lean bridge chain

- `PhysicalPlaquetteGraphResidualFiberBookkeepingTagSpaceInjection1296`
  (`YangMills/ClayCore/LatticeAnimalCount.lean:4090`) is the strongest current
  local source interface.  It asks for a residual bookkeeping/base-zone tag
  space, a residual-value tag extractor on the whole residual subtype, an
  encoding into `Fin 1296`, and selected-admissible tag injectivity for values
  carrying `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`
  evidence from essential parents.
- `physicalPlaquetteGraphResidualFiberSelectorAdmissibleBookkeepingTagInjection1296_of_residualFiberBookkeepingTagSpaceInjection1296`
  (`YangMills/ClayCore/LatticeAnimalCount.lean:4221`) is the exact bridge from
  the tag-space source into
  `PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBookkeepingTagInjection1296`.
- `PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBookkeepingTagInjection1296`
  (`YangMills/ClayCore/LatticeAnimalCount.lean:4164`) is the direct missing
  source named by the v2.208 no-closure attempt.
- `physicalPlaquetteGraphResidualFiberBookkeepingTagAdmissibleValueSeparation1296_of_residualFiberSelectorAdmissibleBookkeepingTagInjection1296`
  (`YangMills/ClayCore/LatticeAnimalCount.lean:4317`) is the exact bridge into
  `PhysicalPlaquetteGraphResidualFiberBookkeepingTagAdmissibleValueSeparation1296`.

### Data carriers and admissibility evidence

- `PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCodeData`
  (`YangMills/ClayCore/LatticeAnimalCount.lean:3942`) is a useful carrier for a
  `bookkeepingTagCode : residual -> Fin 1296`, but it does not construct the
  code or prove selected-admissible separation.
- `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`
  (`YangMills/ClayCore/LatticeAnimalCount.lean:3413`) is the admissibility
  evidence carried by selected terminal-neighbor values.  Its
  `terminalNeighborCode` field is parent/witness-relative and is not a
  residual-subtype bookkeeping tag injection.
- `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296`
  (`YangMills/ClayCore/LatticeAnimalCount.lean:5719`) and theorem
  `physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296`
  (`YangMills/ClayCore/LatticeAnimalCount.lean:5806`) can supply selector-data
  evidence, but they contain no residual bookkeeping tag extractor or tag
  injectivity law.

### Bookkeeping inputs

- `PhysicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296`
  (`YangMills/ClayCore/LatticeAnimalCount.lean:6857`) and theorem
  `physicalPlaquetteGraph_baseAwareTerminalPredecessorBookkeeping1296`
  (`YangMills/ClayCore/LatticeAnimalCount.lean:8379`) supply the v2.121
  deleted/parent/essential/residual-subset bookkeeping inputs.  They are
  admissible hypotheses for a future source theorem, but they do not define a
  selector-independent residual tag space or selected-admissible tag injection.

### Downstream or equivalent interfaces

- `PhysicalPlaquetteGraphResidualFiberBookkeepingTagCoordinate1296`,
  `PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueSeparation1296`,
  `PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueCodeSource1296`, and
  `PhysicalPlaquetteGraphResidualFiberBookkeepingTagCodeForSelector1296` are
  repackaging or downstream targets in the current ladder.  They do not by
  themselves provide the missing source for admissible-value separation.

## Rejected non-candidates

- `finsetCodeOfCardLe` and `finsetCodeOfCardLe_injective`
  (`YangMills/ClayCore/LatticeAnimalCount.lean:438`, `:443`) are not a valid
  proof route here, because the task forbids deriving the code from an already
  bounded selected image or menu.
- Root-shell/root-neighbor code lemmas, including
  `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellCode1296_injective`
  (`YangMills/ClayCore/LatticeAnimalCount.lean:1547`), encode root-shell or
  first-shell data and do not prove residual-subtype bookkeeping tag injectivity.
- Local neighbor, local displacement, and parent-relative terminal-neighbor
  codes are not residual bookkeeping/base-zone tags and cannot serve as
  selected-admissible residual-value separation.
- Selected-image cardinality interfaces, bounded-menu interfaces, empirical
  search evidence, and the v2.161 selector-image cycle remain non-routes.
- The deleted vertex `X` is not a residual terminal neighbor for
  `residual = X.erase (deleted X)`.

## Exact blocker

No existing Lean lemma currently supplies the missing selector-independent
residual bookkeeping/base-zone coordinate source.  The exact next source needed
is:

    PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296

It should produce, before any selected image or bounded menu is supplied:

1. a residual bookkeeping/base-zone tag space,
2. a residual-value tag extractor on the whole residual subtype,
3. an encoding into `Fin 1296`, and
4. selected-admissible tag injectivity for residual values carrying
   `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` evidence
   from essential parents.

## Validation

- Dashboard note records the candidate-lemma map and exact blocker.
- YAML/JSON/JSONL validation is required after registry updates.
- F3-COUNT remains `CONDITIONAL_BRIDGE`; no percentage moved.
