# F3 pointed/base-aware multi-portal interface scope v2.94

**Task:** `CODEX-F3-POINTED-MULTIPORTAL-INTERFACE-SCOPE-001`  
**Date:** 2026-04-27  
**Status:** `SCOPE_DELIVERED_NO_MATH_STATUS_MOVE`

## Purpose

v2.93 showed that the current producer target:

```lean
PhysicalPlaquetteGraphMultiPortalSupportedSafeDeletionOrientation1296x1296
```

is too strict for `k = 2`.  After deleting the only non-root plaquette, the
residual is `{root}`.  The current portal-shell condition then asks the parent
`root` to be supported by a portal `root` through:

```lean
root ∈ (plaquetteGraph physicalClayDimension L).neighborFinset root
```

which is impossible in a simple graph.

This scope defines the next interface shape without claiming a proof.

## Candidate Successor Shapes

### Candidate A: pointed portal shell

Replace the portal-local shell condition with a pointed shell:

```text
parent is either portal itself or a neighbor of portal
```

This handles the singleton residual because `parent = portal = root` is allowed
without pretending that `root` is adjacent to itself.

Cost: the natural finite alphabet is `1 + 1296`, not the old `1296`, unless a
compression theorem is later proved.  This is honest but creates a constants
audit and bridge rewrite burden.

### Candidate B: base-aware multi-portal split

Keep the existing local neighbor machinery for the non-base phase, but split the
first nontrivial residual explicitly:

```text
if residual.card = 1:
  decode deleted directly from the root shell
else:
  decode portal, then parent in portal shell, then deleted in parent shell
```

This avoids self-neighbor support while preserving the existing triple-symbol
decoder target:

```lean
PhysicalPlaquetteGraphDeletedVertexDecoderStep1296x1296x1296
```

In the base branch the middle symbol is unused.  That is acceptable because this
is a larger alphabet route, not a compression theorem.

### Candidate C: larger explicit tagged alphabet

Use an explicit tag plus portal/local/deleted symbols:

```text
base-or-recursive tag x Fin 1296 x Fin 1296 x Fin 1296
```

This is maximally clear but moves further from the currently bridged
triple-symbol target and would need a new decoder contract.

## Recommended Target

Choose Candidate B.

Recommended Lean interface:

```lean
PhysicalPlaquetteGraphBaseAwareMultiPortalSupportedSafeDeletionOrientation1296x1296
```

Suggested proposition shape:

```lean
∀ {L : Nat} [NeZero L]
  (root : ConcretePlaquette physicalClayDimension L) (k : Nat),
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
      portalMenu residual ⊆ residual ∧ (portalMenu residual).card ≤ 1296) ∧
    (∀ residual
      (p : {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual}),
      residual.card ≠ 1 →
        portalOfParent residual p ∈ portalMenu residual ∧
        p.1 ∈ (plaquetteGraph physicalClayDimension L).neighborFinset
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

The final disjunction is load-bearing.  The base branch supplies direct
root-shell support for the deleted plaquette, while the recursive branch supplies
the parent-shell support expected by the existing v2.92 decoder pattern.

## Bridge Target

Recommended bridge theorem:

```lean
physicalPlaquetteGraphDeletedVertexDecoderStep1296x1296x1296_of_baseAwareMultiPortalSupportedSafeDeletionOrientation1296x1296
```

with type:

```lean
PhysicalPlaquetteGraphBaseAwareMultiPortalSupportedSafeDeletionOrientation1296x1296 →
  PhysicalPlaquetteGraphDeletedVertexDecoderStep1296x1296x1296
```

Bridge behavior:

1. The reconstruct function captures `root`, `k`, and the local step code.
2. If `residual.card = 1`, it ignores the portal and parent symbols and decodes
   the deleted plaquette using the third symbol from `root`.
3. If `residual.card ≠ 1`, it follows the v2.92 route: decode portal from the
   residual portal menu, decode parent in the portal shell, decode deleted in the
   parent shell.

This keeps the bridge pointed/base-aware without treating a vertex as adjacent
to itself.

## Why This Avoids The v2.93 Blocker

For `k = 2`, the residual is `{root}` and has cardinality one.  The base branch
does not ask for `root ∈ neighborFinset root`.  It asks only for the deleted
plaquette to be in `neighborFinset root`, which is exactly the ordinary
two-vertex anchored connectivity condition.

For larger residuals, the portal-support condition remains residual-only and
not root-only: the portal menu may move inside the residual, and the parent is
still decoded from a local shell around a residual portal.

## Non-Claims

This scope does not prove:

- the base-aware producer theorem,
- any bridge theorem,
- compression from triple-symbol to `1296x1296`,
- compression from triple-symbol to `1296`,
- F3-COUNT closure.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No percentage, ledger row, README
metric, planner metric, or Clay-level claim moves from this scope.

## Next Lean Task

Recommended next task:

```text
CODEX-F3-BASEAWARE-MULTIPORTAL-INTERFACE-001
```

Add the Lean `Prop` interface
`PhysicalPlaquetteGraphBaseAwareMultiPortalSupportedSafeDeletionOrientation1296x1296`
and, if it builds without `sorry`, add the bridge to
`PhysicalPlaquetteGraphDeletedVertexDecoderStep1296x1296x1296`.
