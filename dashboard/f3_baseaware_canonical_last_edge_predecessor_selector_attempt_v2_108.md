# F3 base-aware canonical last-edge predecessor selector attempt v2.108

**Task:** `CODEX-F3-PROVE-BASEAWARE-CANONICAL-LAST-EDGE-PREDECESSOR-SELECTOR-001`  
**Date:** 2026-04-27  
**Status:** `NO_CLOSURE_SELECTED_LAST_EDGE_IMAGE_BOUND_BLOCKER`

## Attempted target

Codex attempted to prove:

```lean
PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgePredecessorSelector1296
```

No Lean proof was added.

## What the v2.107 interface already gives

The v2.107 interface is a clean bridge interface.  It packages, for every
residual bucket and essential parent `p`, residual-local data:

```lean
PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgeData residual p
```

with:

1. a residual endpoint equal to `p`,
2. a selected residual predecessor,
3. an induced residual walk from predecessor to target,
4. a `Fin 1296` code.

The v2.107 bridge then projects `(predecessor, code)` into:

```lean
PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastStepPredecessorImageBound1296
```

That bridge remains valid and no-sorry.

## Why the selector proof does not close

The current Lean library does not yet provide the load-bearing selected-image
argument needed by the selector.

The existing residual/current-witness helper:

```lean
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_deletedVertex_has_residualNeighborParent
```

can produce an adjacent residual parent for a concrete current bucket and a
concrete deleted vertex.  Using that here would choose predecessor data
post-hoc from `(X, deleted X)`, which is explicitly outside the residual-local
contract.

The root-shell and reachability APIs:

```lean
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_rootShellCode1296_tail_to_member
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_rootShellCode1296_reachable_to_member
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParent1296_reachable
```

provide first-shell reachability from the root.  They do not identify the
terminal predecessor adjacent to an arbitrary essential parent.  Treating a
first-shell plaquette as the last-edge predecessor would confuse reachability
with portal-local adjacency.

Residual preconnectedness can plausibly supply a residual walk to each essential
parent when the residual fiber is nonempty, but the selector needs more than
existence of walks.  It needs a residual-local selection whose predecessor image

```lean
((essential residual).attach.image
  (fun p => (canonicalLastEdgeData residual p).predecessor.1)).card
```

is bounded by `1296`, plus a `Fin 1296` code separating the selected
predecessors.  No current theorem bounds that terminal-predecessor image.  The
physical local degree bound controls the neighbor shell of one fixed plaquette;
it does not bound the number of distinct terminal predecessors selected over an
entire residual essential-parent fiber.

## Exact no-closure blocker

The next missing fact is not another bridge.  It is a bounded-image theorem for
residual-local terminal predecessors:

```text
For every residual fiber, there is a residual-local canonical last-edge
predecessor selection for essential parents whose selected predecessor image has
cardinality <= 1296 and admits an injective Fin 1296 code.
```

Before adding another Lean interface, this should be checked against finite
models: the proof line has repeatedly separated local degree bounds from image
cardinality bounds, so the next useful step is to search whether the selected
last-edge predecessor image can grow beyond `1296`, or isolate the structural
lemma that prevents such growth.

## Validation

Command run:

```bash
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result:

```text
Build completed successfully (8184 jobs).
```

No Lean theorem was added by this no-closure attempt, so no new `#print axioms`
trace was introduced.

## Non-claims

This task does not prove:

- `PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgePredecessorSelector1296`,
- `PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastStepPredecessorImageBound1296`,
- `PhysicalPlaquetteGraphBaseAwareResidualLastStepPortalImageBound1296`,
- `PhysicalPlaquetteGraphBaseAwareResidualPortalMenuBound1296`,
- `PhysicalPlaquetteGraphBaseAwareMultiPortalSupportedSafeDeletionOrientation1296x1296`,
- `PhysicalPlaquetteGraphDeletedVertexDecoderStep1296x1296x1296`,
- any compression to older constants,
- F3-COUNT closure.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`.  No ledger row, project percentage,
README metric, planner metric, or Clay-level claim moves from this task.

## Recommended next task

```text
CODEX-F3-LAST-EDGE-PREDECESSOR-IMAGE-GROWTH-SEARCH-001
```

Search finite residual fibers for growth of the minimum selected last-edge
predecessor image, or isolate the precise structural lemma proving the image
bound without empirical evidence.
