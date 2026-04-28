# F3 base-aware canonical last-step predecessor scope v2.103

**Task:** `CODEX-F3-BASEAWARE-CANONICAL-LAST-STEP-PREDECESSOR-SCOPE-001`  
**Date:** 2026-04-27  
**Status:** `SCOPE_DELIVERED_NO_LEAN_NO_STATUS_MOVE`

## Purpose

v2.102 stopped the direct proof of:

```lean
PhysicalPlaquetteGraphBaseAwareResidualLastStepPortalImageBound1296
```

The blocker is not first-shell reachability, not current-witness adjacency, and
not a local degree estimate.  The missing structural object is a residual-local
canonical last-step predecessor policy: for each residual bucket and essential
parent, choose path/predecessor data from residual-only information, extract the
immediate predecessor adjacent to the essential parent, and prove the selected
predecessor image has cardinality at most `1296`.

## Recommended Lean target

Recommended name:

```lean
PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastStepPredecessorImageBound1296
```

Suggested shape:

```lean
def PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastStepPredecessorImageBound1296 : Prop :=
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
    ∃ canonicalPathData :
      ∀ residual,
        {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual} →
          CanonicalResidualPathData residual p,
    ∃ lastStepPredecessorOf :
      ∀ residual,
        {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual} →
          ConcretePlaquette physicalClayDimension L,
      BaseAwareSafeDeletionChoiceData root k deleted parentOf essential ∧
      (∀ residual,
        essential residual =
          ((plaquetteGraphPreconnectedSubsetsAnchoredCard
              physicalClayDimension L root k).filter
              (fun X => X.erase (deleted X) = residual)).image parentOf) ∧
      CanonicalPathDataExtractsLastStepPredecessor
        canonicalPathData lastStepPredecessorOf ∧
      (∀ residual
        (p : {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual}),
        lastStepPredecessorOf residual p ∈ residual ∧
          (residual.card ≠ 1 →
            p.1 ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset
                (lastStepPredecessorOf residual p))) ∧
      (∀ residual,
        ((essential residual).attach.image
          (fun p => lastStepPredecessorOf residual p)).card ≤ 1296)
```

The names `CanonicalResidualPathData`,
`BaseAwareSafeDeletionChoiceData`, and
`CanonicalPathDataExtractsLastStepPredecessor` are schematic placeholders for
the next Lean-interface task.  The key requirement is that the path/predecessor
data is a separate factor, so the proposition is not merely a renamed copy of
v2.101.

## Non-circular structure

The new target should expose three logically separate burdens:

1. **Safe-deletion branch:** reuse the v2.95/v2.98 base-aware branch with
   `deleted`, `parentOf`, and `essential`.
2. **Canonical residual path/predecessor policy:** from residual-only data and
   an essential parent index, produce canonical path data and its immediate
   last-step predecessor.
3. **Selected-image compression:** prove or expose an injective `Fin 1296` code
   for the image of the selected last-step predecessors over each residual
   fiber.

The selected image:

```lean
(essential residual).attach.image
  (fun p => lastStepPredecessorOf residual p)
```

is the only object whose cardinality should be bounded.  The raw residual
frontier, the residual cardinality, and the local neighbor set of one fixed
portal are all different objects and must not be substituted for it.

## Bridge into v2.101

Exact bridge target:

```lean
physicalPlaquetteGraphBaseAwareResidualLastStepPortalImageBound1296_of_baseAwareResidualCanonicalLastStepPredecessorImageBound1296 :
  PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastStepPredecessorImageBound1296 →
    PhysicalPlaquetteGraphBaseAwareResidualLastStepPortalImageBound1296
```

Bridge idea:

```lean
lastStepPortalOfParent residual p :=
  lastStepPredecessorOf residual p
```

Then repack:

1. selector membership in `residual`,
2. non-singleton adjacency to `p`,
3. selected image bound `≤ 1296`,
4. the existing base-aware safe-deletion branch.

This bridge is honest only if the predecessor target records canonical path or
predecessor data separately.  If the new target simply contains the exact same
fields as v2.101, the stop condition is triggered.

## Why first-shell reachability is still not enough

The current first-shell APIs provide:

```lean
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_rootShellCode1296_tail_to_member
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_rootShellCode1296_reachable_to_member
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParent1296_reachable
```

These can start an induced walk from a bounded root-shell plaquette, but v2.101
needs the immediate predecessor adjacent to the target essential parent.  A
root-shell vertex can be far from that parent, so first-shell reachability cannot
be used as portal-local adjacency.

## Why current-witness adjacency remains forbidden

The current-witness helper:

```lean
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_deletedVertex_has_residualNeighborParent
```

can choose an adjacent residual parent for a concrete deleted vertex in a
current bucket.  That is not residual-only data.  The desired canonical policy
may use residual and essential-parent data, but it must not choose a predecessor
post-hoc from the original `(X, deleted X)` witness.

## Recommended next task

```text
CODEX-F3-BASEAWARE-CANONICAL-LAST-STEP-PREDECESSOR-INTERFACE-001
```

Add a Lean Prop/interface for
`PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastStepPredecessorImageBound1296`
and, only if it builds without `sorry`, prove the bridge into
`PhysicalPlaquetteGraphBaseAwareResidualLastStepPortalImageBound1296`.

## Honesty status

No Lean file was edited in this scope task.  No build was required.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`.  No ledger row, project percentage,
README metric, planner metric, or Clay-level claim moves from this task.
