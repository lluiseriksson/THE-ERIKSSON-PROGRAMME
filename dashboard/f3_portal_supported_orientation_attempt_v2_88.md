# F3 Portal-Supported Orientation Attempt v2.88

Timestamp: 2026-04-27T10:15:00Z

Task: `CODEX-F3-PROVE-PORTAL-SUPPORTED-ORIENTATION-001`

## Target

Attempted target:

```lean
PhysicalPlaquetteGraphPortalSupportedSafeDeletionOrientation1296
```

This is the portal/local-shell theorem introduced in v2.87.  If proved, it
would feed the strengthened product-symbol chain:

```text
PhysicalPlaquetteGraphPortalSupportedSafeDeletionOrientation1296
  -> PhysicalPlaquetteGraphSafeDeletionOrientationCodeBound1296
  -> PhysicalPlaquetteGraphEssentialSafeDeletionParentFrontierBound1296
  -> PhysicalPlaquetteGraphResidualParentMenuBound1296
  -> PhysicalPlaquetteGraphResidualParentMenuCovers1296
  -> PhysicalPlaquetteGraphSymbolicResidualParentSelector1296
  -> PhysicalPlaquetteGraphDeletedVertexDecoderStep1296x1296
```

## Outcome

No proof was added.

The existing file currently provides two separate ingredients:

- safe-deletion existence for anchored buckets, via the non-cut route;
- a root-shell/first-BFS-layer API showing that every nontrivial anchored bucket
  has some member adjacent to the root, with a `Fin 1296` code for that shell.

Those ingredients do not currently intersect.  The cheapest possible portal
strategy would set the residual portal to `root` and choose `parentOf X = root`.
That would make the essential chosen-parent image lie in a single portal-local
shell essentially for free, but it requires the deleted plaquette to be a
root-neighbor:

```lean
z ∈ (plaquetteGraph physicalClayDimension L).neighborFinset root
```

and also requires the same `z` to be a safe deletion:

```lean
X.erase z ∈
  plaquetteGraphPreconnectedSubsetsAnchoredCard
    physicalClayDimension L root (k - 1)
```

The current repository proves these separately, not simultaneously.

## Exact Blocker

The precise missing theorem is a root-shell safe-deletion intersection:

```lean
PhysicalPlaquetteGraphRootShellSafeDeletionExists1296
```

Suggested mathematical content:

```lean
∀ {L : ℕ} [NeZero L]
  {root : ConcretePlaquette physicalClayDimension L} {k : ℕ}
  {X : Finset (ConcretePlaquette physicalClayDimension L)},
  2 ≤ k →
  X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
    physicalClayDimension L root k →
  ∃ z, z ∈ X ∧ z ≠ root ∧
    z ∈ (plaquetteGraph physicalClayDimension L).neighborFinset root ∧
    X.erase z ∈
      plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root (k - 1)
```

If this theorem is true, then the portal-supported orientation theorem can be
proved with:

```text
portal R = if root ∈ R then some root else none
parentOf X = root
essential R = {root} or empty, according to the residual fiber
```

The resulting chosen-parent image is a singleton subset of the residual and is
supported by the portal-local shell around `root`.

## Why Not Close With Existing Theorems

Using `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem`
or `physicalPlaquetteGraphAnchoredSafeDeletionExists` would select a safe
deleted plaquette, but not a portal-local one.

Using the root-shell lemmas around
`physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_rootShellCode1296`
selects a root-neighbor, but does not prove the erased residual stays
preconnected.

Combining them by `Classical.choose` would be a post-hoc existential decoder and
would violate the task stop condition.

## Validation

Command:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result:

```text
Build completed successfully (8184 jobs).
```

No Lean file was changed by this attempt.  No `sorry`; no new project axiom.

## Honesty Status

`F3-COUNT` remains `CONDITIONAL_BRIDGE`.  The strengthened product-symbol route
remains conditional and constants-audit gated.  No ledger row, project
percentage, README metric, planner metric, or Clay-level claim moves from this
attempt.

## Recommended Next Task

```text
CODEX-F3-ROOT-SHELL-SAFE-DELETION-SCOPE-001
```

Objective: state the root-shell safe-deletion intersection as a Lean-stable
proposition or prove a narrower base/structural lemma.  If false, document the
smallest counterexample pattern and return to a more flexible portal policy.
