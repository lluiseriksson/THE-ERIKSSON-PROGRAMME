# F3 base-aware portal-menu bound attempt v2.99

**Task:** `CODEX-F3-PROVE-BASEAWARE-PORTAL-MENU-BOUND-001`  
**Date:** 2026-04-27  
**Status:** `NO_CLOSURE_RESIDUAL_LOCAL_LAST_STEP_PORTAL_IMAGE_BOUND_BLOCKER`

## Target

Codex attempted to prove:

```lean
PhysicalPlaquetteGraphBaseAwareResidualPortalMenuBound1296
```

This is the v2.98 factored bound behind the base-aware multi-portal producer:

```lean
physicalPlaquetteGraphBaseAwareMultiPortalSupportedSafeDeletionOrientation1296x1296_of_baseAwareResidualPortalMenuBound1296
```

## Outcome

No Lean proof was added.  The bound does not close from the current artifacts
without introducing one of the forbidden shortcuts.

The exact missing structure is a residual-local last-step portal image bound:
for each non-singleton residual fiber, construct a residual-only adjacent
predecessor/portal image for the essential parent set and prove that image has
cardinality at most `1296`.

Recommended next theorem name:

```lean
PhysicalPlaquetteGraphBaseAwareResidualLastStepPortalImageBound1296
```

## What works

The v2.98 interface already separates the two branches correctly:

- singleton residuals are handled by the base-aware root-shell branch,
- non-singleton residuals require a residual-only portal menu,
- the bridge to `PhysicalPlaquetteGraphBaseAwareMultiPortalSupportedSafeDeletionOrientation1296x1296`
  is already no-sorry and build-checked.

Existing Lean tools also give useful local ingredients:

```lean
plaquetteGraph_neighborFinset_card_le_physical_ternary
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShell_card_le_1296
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParent1296_reachable
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_deletedVertex_has_residualNeighborParent
```

## Why the direct proof does not close

The root-shell menu route is bounded by `1296`, but it only supplies a
root-shell element that reaches a target member inside the residual-induced
graph.  The v2.98 bound needs a portal-local shell:

```lean
p.1 ∈ (plaquetteGraph physicalClayDimension L).neighborFinset
  (portalOfParent residual p)
```

Reachability to `p` is not enough to prove adjacency to `p`.

The current-witness route supplies a parent adjacent to the deleted plaquette,
but it chooses data from the current `(X, deleted X)` witness.  That violates
the residual-only portal-menu contract.

The last-step route is the honest next shape: select, from residual-only data,
an adjacent predecessor of each essential parent along a canonical residual
path, then prove the image of those selected predecessors has cardinality at
most `1296`.  The current file has reachability APIs, but not the image-card
bound needed for the residual fiber.

## Forbidden shortcuts avoided

This attempt did not:

- use `sorry`,
- add a new project axiom,
- choose portals post-hoc from `(X, deleted X)`,
- set `portalMenu residual = residual`,
- confuse fixed-portal local degree with residual portal-menu cardinality,
- treat bounded empirical search as proof,
- move F3-COUNT or any project percentage.

## Exact next blocker

The next Codex target should scope or add a Lean-stable interface for:

```lean
PhysicalPlaquetteGraphBaseAwareResidualLastStepPortalImageBound1296
```

Intended content:

1. construct base-aware safe-deletion choices as in v2.98,
2. define the essential parent fibers,
3. for each non-singleton residual and each essential parent, choose a portal
   from residual-only data adjacent to that parent,
4. prove the image of all such portals in each residual fiber has cardinality
   at most `1296`,
5. bridge that result to
   `PhysicalPlaquetteGraphBaseAwareResidualPortalMenuBound1296`.

The proof burden must be the bounded image of residual-local adjacent
predecessors, not the raw residual frontier and not the local degree of one
fixed portal.

## Validation

No Lean file was edited in this attempt.  The required build was still run:

```bash
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result:

```text
Build completed successfully (8184 jobs).
```

`F3-COUNT` remains `CONDITIONAL_BRIDGE`.  No ledger row, project percentage,
README metric, planner metric, or Clay-level claim moves from this task.
