# F3 base-aware producer attempt v2.96

**Task:** `CODEX-F3-BASEAWARE-PRODUCER-ATTEMPT-001`  
**Date:** 2026-04-27  
**Status:** `NO_CLOSURE_NONSINGLETON_PORTAL_MENU_BOUND_BLOCKER`

## Target

Attempted producer theorem:

```lean
PhysicalPlaquetteGraphBaseAwareMultiPortalSupportedSafeDeletionOrientation1296x1296
```

This is the producer-side hypothesis for the v2.95 bridge:

```lean
physicalPlaquetteGraphDeletedVertexDecoderStep1296x1296x1296_of_baseAwareMultiPortalSupportedSafeDeletionOrientation1296x1296
```

## Outcome

No Lean proof was added.

The v2.95 interface fixes the v2.93 singleton-residual obstruction: when the
residual has cardinality one, the deleted plaquette is decoded directly from the
root shell, so no proof needs `root ∈ neighborFinset root`.

The remaining blocker is the non-singleton residual branch.  For every residual
bucket, the producer must supply residual-only data:

```lean
portalMenu residual ⊆ residual
(portalMenu residual).card ≤ 1296
```

and every essential parent over that residual fiber must be supported by one of
those portals:

```lean
portalOfParent residual p ∈ portalMenu residual
p.1 ∈ (plaquetteGraph physicalClayDimension L).neighborFinset
  (portalOfParent residual p)
```

Existing Lean artifacts give safe-deletion existence and local parent support
for a current witness `(X, deleted X)`. They do not yet construct a uniformly
bounded residual-only portal menu covering all essential parents in the residual
fiber.

## Why the obvious shortcuts are not valid

Choosing `portalMenu residual = residual` would be residual-only, but it would
need a proof that every relevant residual bucket has cardinality at most `1296`.
That confuses the local degree bound of a fixed plaquette with the size of a
residual bucket or residual fiber; the latter can grow with `k`.

Choosing the portal from the current deleted-vertex witness would give local
support, but it is post-hoc in `(X, deleted X)`, not residual-only. That is
exactly the route excluded by the producer contract and by the task stop
conditions.

Using empirical bounded-search output would also be insufficient: bounded
search can guide the next lemma, but it cannot prove the Lean producer theorem.

## Exact blocker

The missing theorem is a residual-only non-singleton portal-menu bound:

```text
for every residual, construct portalMenu residual ⊆ residual with card ≤ 1296
such that every essential parent over the residual fiber is adjacent to some
portal in portalMenu residual.
```

This should be scoped separately before another producer proof attempt.  A
candidate next Lean target is:

```lean
PhysicalPlaquetteGraphBaseAwareResidualPortalMenuBound1296
```

with a bridge into:

```lean
PhysicalPlaquetteGraphBaseAwareMultiPortalSupportedSafeDeletionOrientation1296x1296
```

The statement must distinguish the bounded essential chosen-parent image from
the raw residual frontier and must not restate the whole producer theorem.

## Validation

No Lean file was edited in this attempt, so no `lake build` was required by the
task validation rule.  The last relevant Lean validation remains the v2.95
build:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
Build completed successfully (8184 jobs).
```

No new theorem, no `sorry`, and no new project axiom were introduced.

## Honesty Status

`F3-COUNT` remains `CONDITIONAL_BRIDGE`.  No ledger row, project percentage,
README metric, planner metric, or Clay-level claim moves from this attempt.

## Next Codex Task

Recommended next task:

```text
CODEX-F3-BASEAWARE-PORTAL-MENU-BOUND-SCOPE-001
```

Scope a Lean-stable non-singleton residual portal-menu bound that can feed the
base-aware producer without post-hoc deleted-vertex choices and without claiming
compression to older constants.
