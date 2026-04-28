# F3 base-aware canonical last-edge predecessor scope v2.106

**Task:** `CODEX-F3-BASEAWARE-CANONICAL-LAST-EDGE-PREDECESSOR-SCOPE-001`  
**Date:** 2026-04-27  
**Status:** `SCOPE_DELIVERED_NO_LEAN_NO_STATUS_MOVE`

## Purpose

v2.105 stopped the direct proof of:

```lean
PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastStepPredecessorImageBound1296
```

The remaining gap is not another root-shell reachability lemma.  The missing
object is a residual-local selector for the last edge of a canonical residual
path to each essential parent.  This selector must produce the immediate
predecessor adjacent to the essential parent, not merely a first neighbor of the
root or a parent chosen after seeing the current deleted-vertex witness.

## Recommended Lean target

Recommended name:

```lean
PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgePredecessorSelector1296
```

Suggested bridge name:

```lean
physicalPlaquetteGraphBaseAwareResidualCanonicalLastStepPredecessorImageBound1296_of_baseAwareResidualCanonicalLastEdgePredecessorSelector1296
```

Bridge target:

```lean
PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastStepPredecessorImageBound1296
```

## Suggested shape

The target should reuse the v2.104 base-aware choices:

```lean
deleted
parentOf
essential
```

and then add a genuinely sharper factorization:

```lean
canonicalLastEdgeData :
  ∀ residual,
    {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual} →
      CanonicalResidualLastEdgeData residual p

canonicalLastStepPredecessor :
  ∀ residual,
    {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual} →
      {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} × Fin 1296
```

The schematic `CanonicalResidualLastEdgeData residual p` should package enough
residual-only data to justify that the selected predecessor is the last vertex
before `p` on a canonical residual path.  It should not contain the whole
current bucket `X`, the deleted plaquette, or a post-hoc witness from the fiber.

The proposition should expose these burdens separately:

1. **Residual-local path choice:** for each residual and essential parent,
   choose canonical residual path/last-edge data depending only on the residual
   and the essential-parent index.
2. **Last-edge extraction:** prove the extracted predecessor lies in the
   residual and is adjacent to the essential parent when `residual.card ≠ 1`.
3. **Code separation:** assign a `Fin 1296` code to selected predecessors and
   prove equal codes force equal selected predecessor vertices.
4. **Selected-image bound:** derive or record that the selected predecessor image
   over each residual fiber has cardinality at most `1296`.

## Why this is sharper than v2.104

v2.104 already contains:

```lean
canonicalLastStepPredecessor residual p :
  {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} × Fin 1296
```

plus adjacency, code separation, and the image bound.  The new target must not
repeat those fields under another name.  It must explain how the predecessor is
obtained by a residual-local canonical last-edge construction.

The future bridge may then project:

```lean
canonicalLastStepPredecessor residual p
```

from the last-edge selector data and repack the v2.104 fields.

## What not to use

The root-shell APIs:

```lean
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_rootShellCode1296_tail_to_member
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_rootShellCode1296_reachable_to_member
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParent1296_reachable
```

are first-shell or reachability tools.  A root-shell vertex can be far from the
target essential parent, so it is not the last-edge predecessor.

The current-witness helper:

```lean
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_deletedVertex_has_residualNeighborParent
```

is also not enough: it provides a neighbor-parent for a concrete deleted
plaquette in a concrete current bucket.  That would choose predecessor data
post-hoc from `(X, deleted X)`, while this route needs residual-local data.

The existing walk splitters:

```lean
simpleGraph_walk_exists_adj_start_of_ne
simpleGraph_walk_exists_adj_start_and_tail_of_ne
```

extract first edges.  The next interface may need either a last-edge splitter
for walks or a canonical path representation whose terminal predecessor is
available by construction.

## Exact bridge route

If the selector target lands, the intended bridge chain is:

```text
PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgePredecessorSelector1296
  -> PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastStepPredecessorImageBound1296
  -> PhysicalPlaquetteGraphBaseAwareResidualLastStepPortalImageBound1296
  -> PhysicalPlaquetteGraphBaseAwareResidualPortalMenuBound1296
  -> PhysicalPlaquetteGraphBaseAwareMultiPortalSupportedSafeDeletionOrientation1296x1296
  -> PhysicalPlaquetteGraphDeletedVertexDecoderStep1296x1296x1296
```

This remains a strengthened triple-symbol route.  It does not compress to the
old `Fin 1296` or `Fin 1296 × Fin 1296` constants.

## Recommended next task

```text
CODEX-F3-BASEAWARE-CANONICAL-LAST-EDGE-PREDECESSOR-INTERFACE-001
```

Add a Lean Prop/interface for
`PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgePredecessorSelector1296`
and, only if it builds without `sorry`, a bridge into
`PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastStepPredecessorImageBound1296`.

## Honesty status

No Lean file was edited in this scope task.  No build was required.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`.  No ledger row, project percentage,
README metric, planner metric, or Clay-level claim moves from this task.
