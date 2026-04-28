# F3 multi-portal orientation attempt v2.93

**Task:** `CODEX-F3-PROVE-MULTIPORTAL-ORIENTATION-001`  
**Date:** 2026-04-27  
**Status:** `NO_CLOSURE_BASE_CASE_PORTAL_SELF_NEIGHBOR_BLOCKER`

## Target

Attempted target:

```lean
PhysicalPlaquetteGraphMultiPortalSupportedSafeDeletionOrientation1296x1296
```

This proposition is the producer-side theorem needed by the v2.92 bridge:

```lean
physicalPlaquetteGraphDeletedVertexDecoderStep1296x1296x1296_of_multiPortalSupportedSafeDeletionOrientation1296x1296
```

## Outcome

No proof was added.

The current multi-portal interface is too strong in the first nontrivial case.
For `k = 2`, an anchored bucket has shape:

```text
X = {root, z}
```

After the only valid safe deletion, the residual is:

```text
residual = {root}
```

The current interface requires:

```lean
parentOf X ∈ X.erase (deleted X)
```

so the only possible parent is:

```text
parentOf X = root
```

It also requires a residual-only portal menu:

```lean
portalMenu residual ⊆ residual
```

and every essential parent must be supported by a portal-local shell:

```lean
p.1 ∈ (plaquetteGraph physicalClayDimension L).neighborFinset
  (portalOfParent residual p)
```

For the singleton residual, any portal drawn from `portalMenu residual` is forced
to be `root`, so the shell condition would require:

```text
root ∈ neighborFinset root
```

That is impossible for the simple plaquette graph: the neighbor relation excludes
self-neighbors. This is the same structural issue as asking a local-neighbor code
to encode `parent = portal` by an actual edge.

## Why This Is Not A Lean Refutation

This note does not add a formal theorem proving the negation of the proposition.
It records a hand-checkable obstruction in the interface shape. A formal
refutation would also require constructing a concrete nonempty physical
two-plaquette anchored bucket for a chosen `L` and `root`.

The stop condition is nevertheless triggered for this task: a proof of the
current proposition would require papering over the base-case self-neighbor
obstruction, changing the interface, or using an unverified shortcut.

## Validation

Command run:

```bash
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result:

```text
Build completed successfully (8184 jobs).
```

No Lean file was edited in this attempt. No new theorem, no `sorry`, and no new
project axiom were introduced.

## Required Successor Interface

The next interface should make the base case explicit instead of trying to force
it through a neighbor shell. Two viable shapes:

1. **Pointed portal shell:** allow a first component that selects a portal and a
   second component that selects either the portal itself or one of its local
   neighbors. This is morally `Option (neighbor portal)` or a finite pointed
   shell of size at most `1297`, requiring a constants audit if kept exact.
2. **Base-aware multi-portal route:** split the `k = 2` case out using the
   existing base-case decoder machinery, and use the multi-portal shell only for
   residuals with cardinality at least two.

Recommended next target:

```text
CODEX-F3-POINTED-MULTIPORTAL-INTERFACE-SCOPE-001
```

Scope a Lean-stable successor proposition that handles the singleton residual
without reintroducing root-only behavior, without post-hoc deleted-vertex
choices, and without claiming compression to the old `1296` or `1296x1296`
constants.

## Honesty Status

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No ledger row, project percentage,
README metric, planner metric, or Clay-level claim moves from this attempt.
