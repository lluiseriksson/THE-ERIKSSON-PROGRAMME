# F3 base-aware canonical last-step predecessor bound attempt v2.105

**Task:** `CODEX-F3-PROVE-BASEAWARE-CANONICAL-LAST-STEP-PREDECESSOR-IMAGE-BOUND-001`  
**Date:** 2026-04-27  
**Status:** `NO_CLOSURE_CANONICAL_LAST_EDGE_PREDECESSOR_SELECTOR_BLOCKER`

## Attempted target

Codex attempted to prove:

```lean
PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastStepPredecessorImageBound1296
```

No Lean proof was added.

## Why the proof stops

The v2.104 interface requires residual-local coded predecessor data:

```lean
canonicalLastStepPredecessor residual p :
  {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} × Fin 1296
```

for each essential parent `p`, together with:

1. `q ∈ residual`,
2. non-singleton portal-local adjacency from `q` to `p`,
3. `Fin 1296` code separation for selected predecessors,
4. a selected predecessor image bound `≤ 1296`.

The existing APIs do not provide this object.

## Existing tools checked

The root-shell APIs:

```lean
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_rootShellCode1296_tail_to_member
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_rootShellCode1296_reachable_to_member
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParent1296_reachable
```

provide bounded first-shell reachability data from the root side.  They do not
provide the immediate predecessor adjacent to an arbitrary essential parent.
Using a first root-shell step as if it were the last predecessor would confuse
reachability with portal-local adjacency.

The current-witness helper:

```lean
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_deletedVertex_has_residualNeighborParent
```

does provide an adjacent residual parent for a concrete deleted vertex in a
current bucket, but that is selected from the current `(X, deleted X)` witness.
The task explicitly forbids using that as the residual-local predecessor policy.

The walk splitting helpers:

```lean
simpleGraph_walk_exists_adj_start_of_ne
simpleGraph_walk_exists_adj_start_and_tail_of_ne
```

extract a first edge from a nontrivial walk.  The missing data here is a
residual-local last-edge predecessor for each essential parent, plus a code and
image-cardinality argument.  There is no current Lean theorem that packages
that last-edge selector independently of the current deleted-vertex witness.

## Exact blocker

The next mathematical target should isolate a residual-local canonical
last-edge predecessor selector:

```lean
PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgePredecessorSelector1296
```

Suggested bridge:

```lean
physicalPlaquetteGraphBaseAwareResidualCanonicalLastStepPredecessorImageBound1296_of_baseAwareResidualCanonicalLastEdgePredecessorSelector1296 :
  PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgePredecessorSelector1296 →
    PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastStepPredecessorImageBound1296
```

The selector target should expose:

1. residual-local canonical path or last-edge data for each essential parent,
2. extraction of the immediate predecessor adjacent to the essential parent,
3. a `Fin 1296` code separating selected predecessors inside each residual fiber,
4. a selected-image cardinality proof derived from that code.

This is sharper than v2.104: it must explain how the predecessor is obtained,
not merely carry the selected predecessor and its image bound as assumptions.

## Validation

Command run for this proof attempt:

```bash
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result:

```text
Build completed successfully (8184 jobs).
```

No Lean file was changed by this no-closure attempt, so no new theorem or new
axiom trace was introduced.

## Non-claims

This task does not prove:

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
CODEX-F3-BASEAWARE-CANONICAL-LAST-EDGE-PREDECESSOR-SCOPE-001
```

Scope the Lean-stable selector
`PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgePredecessorSelector1296`
and its bridge into the v2.104 canonical last-step predecessor image bound.
