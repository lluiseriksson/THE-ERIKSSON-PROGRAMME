# F3 base-aware portal-menu bound scope v2.97

**Task:** `CODEX-F3-BASEAWARE-PORTAL-MENU-BOUND-SCOPE-001`  
**Date:** 2026-04-27  
**Status:** `SCOPE_DELIVERED_NO_LEAN_NO_STATUS_MOVE`

## Purpose

v2.96 stopped the direct producer attempt for:

```lean
PhysicalPlaquetteGraphBaseAwareMultiPortalSupportedSafeDeletionOrientation1296x1296
```

The singleton residual branch is no longer the problem.  The missing structure
is the non-singleton portal-menu cover:

```text
residual-only portal menu, card <= 1296,
covering all essential parents over the residual fiber.
```

This note scopes a sharper Lean target for that missing structure without
claiming a proof.

## Why not reuse older targets directly

`PhysicalPlaquetteGraphResidualParentMenuBound1296` bounds a residual parent
menu for the earlier symbolic-parent route.  It is useful precedent, but the
v2.95 base-aware producer needs a different object:

```text
portal menu in the residual,
then parent in a portal-local shell,
then deleted plaquette in a parent-local shell.
```

`PhysicalPlaquetteGraphMultiPortalSupportedSafeDeletionOrientation1296x1296`
has almost this shape, but it is too strict at singleton residuals and was
blocked at v2.93.  The base-aware route should not go back to that proposition.

The new target should isolate only the non-singleton portal cover while leaving
the singleton branch to the v2.95 root-shell decoder.

## Proposed Lean target

Recommended name:

```lean
PhysicalPlaquetteGraphBaseAwareResidualPortalMenuBound1296
```

Suggested proposition shape:

```lean
∀ {L : ℕ} [NeZero L]
  (root : ConcretePlaquette physicalClayDimension L) (k : ℕ),
  ∃ deleted :
    Finset (ConcretePlaquette physicalClayDimension L) →
      ConcretePlaquette physicalClayDimension L,
  ∃ parentOf :
    Finset (ConcretePlaquette physicalClayDimension L) →
      ConcretePlaquette physicalClayDimension L,
  ∃ essential :
    Finset (ConcretePlaquette physicalClayDimension L) →
      Finset (ConcretePlaquette physicalClayDimension L),
  ∃ portalMenu :
    Finset (ConcretePlaquette physicalClayDimension L) →
      Finset (ConcretePlaquette physicalClayDimension L),
  ∃ portalOfParent :
    ∀ residual,
      {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual} →
        ConcretePlaquette physicalClayDimension L,
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) ∧
    (∀ residual,
      portalMenu residual ⊆ residual ∧
        (portalMenu residual).card ≤ 1296) ∧
    (∀ residual
      (p : {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual}),
      residual.card ≠ 1 →
        portalOfParent residual p ∈ portalMenu residual ∧
          p.1 ∈
            (plaquetteGraph physicalClayDimension L).neighborFinset
              (portalOfParent residual p)) ∧
    ∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        ((X.erase (deleted X)).card = 1 ∧
          parentOf X = root ∧
          deleted X ∈
            (plaquetteGraph physicalClayDimension L).neighborFinset root ∨
         (X.erase (deleted X)).card ≠ 1 ∧
          deleted X ∈
            (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X))
```

This is close to the v2.95 producer, but its intended proof burden is
narrower: the singleton branch is inherited from root-shell decoding, while the
new mathematical content is only the non-singleton residual portal-menu cover.
When formalized, the Lean comment should make that proof burden explicit so the
target is not mistaken for a closed producer theorem.

## Bridge target

The exact bridge should be:

```lean
physicalPlaquetteGraphBaseAwareMultiPortalSupportedSafeDeletionOrientation1296x1296_of_baseAwareResidualPortalMenuBound1296 :
  PhysicalPlaquetteGraphBaseAwareResidualPortalMenuBound1296 →
    PhysicalPlaquetteGraphBaseAwareMultiPortalSupportedSafeDeletionOrientation1296x1296
```

The bridge is expected to be structurally direct: unpack the bounded
non-singleton portal-menu data and repack it as the v2.95 producer interface.
It must not bridge to the older strict multi-portal proposition and must not
claim compression to `Fin 1296` or `Fin 1296 × Fin 1296`.

## What the proof must establish

The future proof must construct `portalMenu residual` from residual-only data.
For every non-singleton residual, the menu must:

1. be a subset of the residual,
2. have cardinality at most `1296`,
3. cover every essential parent in the residual fiber by a portal-local neighbor
   shell.

The essential parent set is the image of `parentOf` over current buckets whose
chosen deletion produces the same residual.  This is not the raw residual
frontier and not the whole residual bucket.

## Non-goals and forbidden shortcuts

This scope does not prove the bound.

It also does not allow:

- choosing portals from the current `(X, deleted X)` witness,
- setting `portalMenu residual = residual` without a genuine `card <= 1296`
  argument for the menu,
- using bounded empirical search as proof,
- reverting to the strict v2.91/v2.93 multi-portal producer,
- moving F3-COUNT, percentages, or Clay-level claims.

## Recommended next task

```text
CODEX-F3-BASEAWARE-PORTAL-MENU-BOUND-INTERFACE-001
```

Add the Lean `Prop` interface
`PhysicalPlaquetteGraphBaseAwareResidualPortalMenuBound1296` and, if it builds
without `sorry`, add the direct bridge into
`PhysicalPlaquetteGraphBaseAwareMultiPortalSupportedSafeDeletionOrientation1296x1296`.

## Honesty Status

`F3-COUNT` remains `CONDITIONAL_BRIDGE`.  No ledger row, project percentage,
README metric, planner metric, or Clay-level claim moves from this scope.
