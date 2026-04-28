# F3 last-edge dominating-set lemma scope v2.110

**Task:** `CODEX-F3-LAST-EDGE-DOMINATING-SET-LEMMA-SCOPE-001`  
**Date:** 2026-04-27  
**Status:** `SCOPE_DELIVERED_NO_LEAN_NO_STATUS_MOVE`

## Purpose

The v2.107 interface:

```lean
PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgePredecessorSelector1296
```

already contains the right decoder-facing shape: for every residual bucket and
essential parent it asks for residual-local last-edge data, a selected
predecessor, and a `Fin 1296` code.  The v2.108 proof attempt showed that the
remaining missing content is not another decoder bridge, but an honest bound on
the selected terminal-predecessor image.  The v2.109 search found bounded
no-growth evidence, but that evidence is not a proof.

This scope isolates the next structural target.

## Proposed Lean target

Recommended proposition name:

```lean
PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296
```

Intended shape:

```lean
def PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296 : Prop :=
  forall {L : Nat} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : Nat),
    exists deleted :
      Finset (ConcretePlaquette physicalClayDimension L) ->
        ConcretePlaquette physicalClayDimension L,
    exists parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) ->
        ConcretePlaquette physicalClayDimension L,
    exists essential :
      Finset (ConcretePlaquette physicalClayDimension L) ->
        Finset (ConcretePlaquette physicalClayDimension L),
    exists terminalPredMenu :
      Finset (ConcretePlaquette physicalClayDimension L) ->
        Finset (ConcretePlaquette physicalClayDimension L),
    exists terminalPredOfParent :
      forall residual,
        {p : ConcretePlaquette physicalClayDimension L // p in essential residual} ->
          ConcretePlaquette physicalClayDimension L,
    exists terminalPredCode :
      forall residual,
        {q : ConcretePlaquette physicalClayDimension L // q in terminalPredMenu residual} ->
          Fin 1296,
      -- Same base-aware safe-deletion/parent branch as v2.107.
      baseAwareChoice deleted parentOf essential root k /\
      -- Essential parents are exactly the parent image over the chosen-deletion
      -- residual fiber.
      essentialImage deleted parentOf essential root k /\
      -- The selected predecessor menu is residual-only and 1296-coded.
      (forall residual,
        terminalPredMenu residual subset residual /\
        Function.Injective (terminalPredCode residual)) /\
      -- The selected predecessor image is exactly the terminalPredOfParent image.
      (forall residual,
        terminalPredMenu residual =
          (essential residual).attach.image
            (fun p => terminalPredOfParent residual p)) /\
      -- Last-edge domination: every non-singleton essential parent is adjacent
      -- to its selected terminal predecessor.
      (forall residual p,
        residual.card != 1 ->
          terminalPredOfParent residual p in terminalPredMenu residual /\
          p.1 in (plaquetteGraph physicalClayDimension L).neighborFinset
            (terminalPredOfParent residual p))
```

The placeholder names `baseAwareChoice` and `essentialImage` are not proposed
new definitions; they indicate reuse of the exact clauses already present in
`PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgePredecessorSelector1296`.

## Exact bridge target

The bridge should target:

```lean
PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgePredecessorSelector1296
```

Recommended bridge theorem name:

```lean
physicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgePredecessorSelector1296_of_residualLastEdgeDominatingSetBound1296
```

Bridge idea:

1. reuse `deleted`, `parentOf`, and `essential` from the domination lemma;
2. set `canonicalLastEdgeData residual p` with:
   - `target := ⟨p.1, ...⟩`,
   - `predecessor := ⟨terminalPredOfParent residual p, ...⟩`,
   - `code := terminalPredCode residual ⟨terminalPredOfParent residual p, ...⟩`;
3. provide a residual induced walk from selected predecessor to target.

The only extra proof ingredient the bridge still needs is the last-edge walk
constructor:

```text
If q and p are both in residual and p is in neighborFinset q, then there is an
induced residual walk from q to p.
```

That helper is small and graph-theoretic; it is not the mathematical bottleneck.
The load-bearing part is the residual-only construction and coding of
`terminalPredMenu`.

## Why this is sharper than v2.107

This target does not merely restate
`PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgePredecessorSelector1296`.
It factors the selected-image requirement through a residual-only dominating
set:

```text
terminalPredMenu residual
```

The v2.107 selector directly asks for all `canonicalLastEdgeData` and then
states:

```lean
((essential residual).attach.image
  (fun p => (canonicalLastEdgeData residual p).predecessor.1)).card <= 1296
```

The scoped lemma instead requires a named residual-only menu with an injective
`Fin 1296` code and then asks the last-edge data to project through that menu.
That is a separate selected-image structure.

## Explicit distinctions

The proposed lemma bounds selected terminal-predecessor image cardinality.  It
does not bound:

- raw residual frontier growth,
- residual cardinality,
- local degree of one fixed portal,
- first-shell/root reachability.

The selected predecessors must be residual-local.  They cannot be chosen
post-hoc from a current `(X, deleted X)` witness.

The v2.109 bounded search motivates this direction, but is not used as proof.

## Recommended next task

```text
CODEX-F3-LAST-EDGE-DOMINATING-SET-INTERFACE-001
```

Add a Lean Prop/interface for
`PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296` and, if it builds
without `sorry`, add the bridge to
`PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgePredecessorSelector1296`.

## Non-claims

This task does not prove:

- `PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296`,
- `PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgePredecessorSelector1296`,
- `PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastStepPredecessorImageBound1296`,
- `PhysicalPlaquetteGraphDeletedVertexDecoderStep1296x1296x1296`,
- any compression to older constants,
- F3-COUNT closure.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`.  No ledger row, project percentage,
README metric, planner metric, or Clay-level claim moves from this task.
