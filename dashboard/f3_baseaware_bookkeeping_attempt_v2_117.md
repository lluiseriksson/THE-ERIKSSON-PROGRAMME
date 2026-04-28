# F3 base-aware bookkeeping proof attempt v2.117

**Task:** `CODEX-F3-PROVE-BASEAWARE-BOOKKEEPING-001`  
**Date:** 2026-04-27  
**Status:** no closure; low-cardinality totalization blocker isolated.

## Attempted target

```lean
PhysicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296
```

The v2.116 interface asks for total functions:

```lean
deleted
parentOf
essential
```

and three proof blocks:

- safe-deletion and parent bookkeeping for each current anchored bucket when `2 <= k`;
- the exact fiber identity
  `essential residual = (fiber of X.erase (deleted X) = residual).image parentOf`;
- the global subset fact `essential residual ⊆ residual`.

## Existing ingredients that almost prove the high-cardinality branch

For the `2 <= k` branch, the existing APIs provide the needed safe deletion and
current-bucket parent witness:

```lean
physicalPlaquetteGraphAnchoredSafeDeletionExists
```

feeds:

```lean
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem
```

and after choosing a deleted non-root plaquette, the residual parent comes from:

```lean
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_deletedVertex_has_residualNeighborParent
```

This is enough to define `deleted X` and `parentOf X` honestly for buckets in:

```lean
X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard physicalClayDimension L root k
```

under the theorem hypothesis:

```lean
2 <= k
```

No terminal predecessor menu or post-hoc terminal predecessor choice is needed for
this high-cardinality branch.

## Exact no-closure blocker

The blocker is not the safe-deletion branch itself.  It is the total
`essential residual ⊆ residual` clause in the v2.116 interface.

That clause is quantified over every `k` and every residual:

```lean
forall residual, essential residual ⊆ residual
```

but the safe-deletion construction is only available in the current-bucket
clause under:

```lean
2 <= k
```

The fiber identity is also unguarded:

```lean
essential residual =
  ((plaquetteGraphPreconnectedSubsetsAnchoredCard
    physicalClayDimension L root k).filter
    (fun X => X.erase (deleted X) = residual)).image parentOf
```

So for `k < 2`, the proof still has to define total values of `deleted X` and
`parentOf X` such that every parent in that image lies in the residual
`X.erase (deleted X)`.  Existing safe-deletion APIs do not provide this, because
they intentionally start at `2 <= k`.

The smallest problematic shape is the `k = 1` anchored singleton bucket.  To make
the unguarded subset clause true with the image definition above, one would need a
low-cardinality totalization such as:

```lean
parentOf X = root
deleted X ∉ X
```

so that:

```lean
root ∈ X.erase (deleted X)
```

This requires a separate Lean proof that an appropriate non-root plaquette can be
chosen uniformly, and that the `k = 0` fiber is empty or otherwise harmless.  That
is not supplied by the current safe-deletion/residual-fiber APIs.

## Why no Lean theorem was added

Adding a proof now would require one of the following unproved moves:

- a low-cardinality default deleted plaquette not lying in singleton anchored
  buckets;
- a proof that all `k = 0` fibers are empty and all `k = 1` fibers can be
  totalized as above;
- weakening or guarding the v2.116 `essential` fiber identity and subset clauses.

None of these is presently established in Lean.  Using an arbitrary default would
make the image/subset proof fail or hide a new unproved base-case obligation.

## Next exact target

The next task should isolate the low-cardinality totalization separately:

```lean
PhysicalPlaquetteGraphBaseAwareLowCardBookkeepingTotalization1296
```

or an equivalent guarded-bookkeeping revision.  The target should prove, without
`sorry`, one of:

- the `k < 2` residual fibers are empty or harmless for the unguarded image;
- for `k = 1`, there is a uniform non-root `deleted X` with `parentOf X = root`
  and `parentOf X ∈ X.erase (deleted X)`;
- the interface/bridge can be safely guarded so terminal-domination is invoked
  only on `2 <= k` fibers needed by the deletion step.

## Validation

No Lean file was edited in this v2.117 attempt.

`lake build YangMills.ClayCore.LatticeAnimalCount` was run after this note and
passed.

## Non-claims

This task does not prove:

- `PhysicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296`;
- `PhysicalPlaquetteGraphResidualTerminalPredecessorDomination1296`;
- `PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296`;
- any decoder compression to an older constant.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No ledger status, project percentage,
README metric, planner metric, or Clay-level claim moved.
