# F3 base-aware last-step portal image scope v2.100

**Task:** `CODEX-F3-BASEAWARE-LAST-STEP-PORTAL-IMAGE-SCOPE-001`  
**Date:** 2026-04-27  
**Status:** `SCOPE_DELIVERED_NO_LEAN_NO_STATUS_MOVE`

## Purpose

v2.99 stopped the direct proof of:

```lean
PhysicalPlaquetteGraphBaseAwareResidualPortalMenuBound1296
```

The missing point is not the singleton residual case and not local degree.  The
missing point is a residual-local last-step portal image bound: for each
non-singleton residual fiber, choose portals from residual-only data that are
adjacent to essential parents, then prove the selected portal image has
cardinality at most `1296`.

## Proposed Lean target

Recommended name:

```lean
PhysicalPlaquetteGraphBaseAwareResidualLastStepPortalImageBound1296
```

Suggested shape:

```lean
def PhysicalPlaquetteGraphBaseAwareResidualLastStepPortalImageBound1296 : Prop :=
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
    ∃ lastStepPortalOfParent :
      ∀ residual,
        {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual} →
          ConcretePlaquette physicalClayDimension L,
      BaseAwareSafeDeletionChoiceData root k deleted parentOf essential ∧
      (∀ residual,
        essential residual =
          ((plaquetteGraphPreconnectedSubsetsAnchoredCard
              physicalClayDimension L root k).filter
              (fun X => X.erase (deleted X) = residual)).image parentOf) ∧
      (∀ residual
        (p : {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual}),
        residual.card ≠ 1 →
          lastStepPortalOfParent residual p ∈ residual ∧
          p.1 ∈
            (plaquetteGraph physicalClayDimension L).neighborFinset
              (lastStepPortalOfParent residual p)) ∧
      (∀ residual,
        ((essential residual).attach.image
          (fun p => lastStepPortalOfParent residual p)).card ≤ 1296)
```

`BaseAwareSafeDeletionChoiceData` is written here as a placeholder for the
already-present v2.98 `deleted` / `parentOf` branch condition.  The next Lean
interface task may either factor that repeated condition into a local helper
definition or inline it exactly as v2.98 does.

The important new object is:

```lean
lastStepPortalOfParent residual p
```

It is residual-local and parent-indexed.  Its image, not the whole residual and
not the raw residual frontier, becomes the portal menu.

## Bridge to v2.98 bound

Exact bridge target:

```lean
physicalPlaquetteGraphBaseAwareResidualPortalMenuBound1296_of_baseAwareResidualLastStepPortalImageBound1296 :
  PhysicalPlaquetteGraphBaseAwareResidualLastStepPortalImageBound1296 →
    PhysicalPlaquetteGraphBaseAwareResidualPortalMenuBound1296
```

Bridge idea:

```lean
portalMenu residual :=
  (essential residual).attach.image
    (fun p => lastStepPortalOfParent residual p)

portalOfParent residual p :=
  lastStepPortalOfParent residual p
```

The bridge then proves:

1. `portalMenu residual ⊆ residual` from the portal-membership clause,
2. `(portalMenu residual).card ≤ 1296` from the image bound,
3. portal-local support from the adjacency clause,
4. the v2.98 safe-deletion branch by repacking the shared choice data.

This is a real bridge because the new target asks for a bounded image of
selected last-step portals.  It is not just v2.98 restated with different
variable names.

## Why root-shell reachability is insufficient

Existing APIs such as:

```lean
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParent1296_reachable
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_rootShellCode1296_tail_to_member
```

show that a bounded root-shell element can reach a target member inside the
residual-induced graph.  The v2.98 portal-menu contract needs:

```lean
p.1 ∈ (plaquetteGraph physicalClayDimension L).neighborFinset
  (portalOfParent residual p)
```

Reachability is not adjacency.  The last-step portal must be the predecessor
adjacent to `p`, not merely the first shell vertex that starts a path to `p`.

## Why local degree is insufficient

`plaquetteGraph_neighborFinset_card_le_physical_ternary` bounds the neighbor
set of one fixed portal by `1296`.  The v2.98 bound asks how many portals are
needed to cover all essential parents in a residual fiber.  Those are different
cardinality problems:

- local degree: fixed `portal`, count possible neighbors,
- selected image bound: fixed `residual`, count selected portals over essential
  parents,
- raw residual size: count all residual plaquettes, which may grow with `k`.

The proposed target bounds only the selected image.

## Why current-witness portals are forbidden

`physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_deletedVertex_has_residualNeighborParent`
gives local adjacency for a concrete current bucket and deleted vertex.  It does
not produce a portal menu from residual-only data.  Using that theorem to pick a
portal separately for each `(X, deleted X)` witness would be post-hoc and would
not satisfy the residual-only contract.

## Recommended next task

```text
CODEX-F3-BASEAWARE-LAST-STEP-PORTAL-IMAGE-INTERFACE-001
```

Add the Lean `Prop` interface
`PhysicalPlaquetteGraphBaseAwareResidualLastStepPortalImageBound1296` and, if it
builds without `sorry`, prove the bridge:

```lean
physicalPlaquetteGraphBaseAwareResidualPortalMenuBound1296_of_baseAwareResidualLastStepPortalImageBound1296
```

No proof of the image bound should be claimed by that interface task.

## Honesty status

No Lean file was edited in this scope task.  No build was required.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`.  No ledger row, project percentage,
README metric, planner metric, or Clay-level claim moves from this task.
