# F3 base-aware last-step portal image bound attempt v2.102

**Task:** `CODEX-F3-PROVE-BASEAWARE-LAST-STEP-PORTAL-IMAGE-BOUND-001`  
**Date:** 2026-04-27  
**Status:** `NO_CLOSURE_CANONICAL_LAST_STEP_PREDECESSOR_IMAGE_BLOCKER`

## Attempted target

Codex attempted to prove:

```lean
PhysicalPlaquetteGraphBaseAwareResidualLastStepPortalImageBound1296
```

No Lean theorem was added in this attempt.

## Outcome

The proof does not close from the current API without crossing a stop
condition.  The exact missing step is a residual-local canonical last-step
predecessor policy whose selected predecessor image is bounded by `1296`.

The v2.101 interface already states the desired final object:

```lean
lastStepPortalOfParent residual p
```

with:

1. `lastStepPortalOfParent residual p ∈ residual`,
2. non-singleton portal-local adjacency from that portal to `p`,
3. selected image cardinality at most `1296`.

The current library has reachability and current-witness adjacency ingredients,
but not the residual-local last-step extraction plus image bound needed to
produce that object.

## Why the direct proof stops

### Root-shell reachability is not enough

The existing first-shell APIs:

```lean
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_rootShellCode1296_tail_to_member
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_rootShellCode1296_reachable_to_member
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParent1296_reachable
```

give a bounded root-shell starting point and a walk or reachability relation to
a target member.  The v2.101 target needs the last predecessor adjacent to the
essential parent.  Treating the first root-shell plaquette as the portal would
confuse reachability with adjacency and triggers the explicit stop condition.

### Current-witness adjacency is not residual-local

The existing deleted-vertex helper:

```lean
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_deletedVertex_has_residualNeighborParent
```

does give an adjacent residual parent for a concrete `(X, deleted X)` witness.
Using it here would choose a portal post-hoc from the current bucket and deleted
vertex, not from residual-only data.  That is exactly the forbidden route.

### Local degree is the wrong cardinality

The physical neighbor bound controls:

```lean
(plaquetteGraph physicalClayDimension L).neighborFinset portal
```

for one fixed portal.  The current target asks for the cardinality of the image:

```lean
(essential residual).attach.image
  (fun p => lastStepPortalOfParent residual p)
```

over the whole essential parent fiber.  The proof needs a bound on this selected
image, not on raw residual size, raw residual frontier growth, or the local
degree of one fixed portal.

## Exact next blocker

Recommended next structural target:

```lean
PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastStepPredecessorImageBound1296
```

This should not simply restate
`PhysicalPlaquetteGraphBaseAwareResidualLastStepPortalImageBound1296`.  It should
factor the missing argument through explicit residual-local path data:

1. a residual-only canonical path or predecessor policy for each essential
   parent,
2. extraction of the immediate predecessor adjacent to the essential parent for
   non-singleton residuals,
3. a finite code or image argument proving that the selected predecessor image
   has cardinality at most `1296`,
4. a no-sorry bridge into
   `PhysicalPlaquetteGraphBaseAwareResidualLastStepPortalImageBound1296`.

The bridge should have the intended shape:

```lean
physicalPlaquetteGraphBaseAwareResidualLastStepPortalImageBound1296_of_baseAwareResidualCanonicalLastStepPredecessorImageBound1296 :
  PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastStepPredecessorImageBound1296 →
    PhysicalPlaquetteGraphBaseAwareResidualLastStepPortalImageBound1296
```

## Validation

Required command:

```bash
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result recorded after this note:

```text
Build completed successfully.
```

No new Lean theorem was added by this attempt, so no new `#print axioms` trace
is required.

## Non-claims

This task does not prove:

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
CODEX-F3-BASEAWARE-CANONICAL-LAST-STEP-PREDECESSOR-SCOPE-001
```

Scope the residual-local canonical last-step predecessor policy and the exact
image-cardinality argument needed to bridge into v2.101.
