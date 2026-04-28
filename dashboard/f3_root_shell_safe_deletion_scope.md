# F3 Root-Shell Safe-Deletion Scope v2.89

Timestamp: 2026-04-27T10:30:00Z

Task: `CODEX-F3-ROOT-SHELL-SAFE-DELETION-SCOPE-001`

## Lean Interface

Added the Lean-stable proposition:

```lean
PhysicalPlaquetteGraphRootShellSafeDeletionExists1296
```

Location:

```text
YangMills/ClayCore/LatticeAnimalCount.lean:2972
```

The proposition asks for one deleted plaquette `z` that simultaneously satisfies:

```lean
z ∈ X
z ≠ root
z ∈ (plaquetteGraph physicalClayDimension L).neighborFinset root
X.erase z ∈
  plaquetteGraphPreconnectedSubsetsAnchoredCard
    physicalClayDimension L root (k - 1)
```

This is strictly stronger than the two existing ingredients:

- root-shell nonemptiness, which gives some `z` adjacent to the root;
- safe-deletion existence, which gives some safe `z`.

The scope does not treat those separate witnesses as proving their
intersection.

## Smallest Counterexample Pattern

The root-shell safe-deletion intersection is not a valid theorem for arbitrary
connected graph animals.  The minimal abstract pattern is the 3-vertex path:

```text
root -- a -- b
```

With anchored bucket `X = {root, a, b}`:

- the root shell is `{a}`;
- deleting `a` leaves `{root, b}`, which is disconnected in the induced graph;
- deleting `b` is safe, but `b` is not adjacent to `root`.

Thus the cheap portal policy

```text
portal residual = some root
parentOf X = root
```

cannot be the general strategy unless the physical plaquette graph has an
additional structural restriction excluding this pattern.  No such restriction
is currently present in `LatticeAnimalCount.lean`.

This is a hand-checkable graph-theoretic obstruction pattern, not a Lean
refutation theorem for the full physical plaquette model.

## Bridge To v2.87

If `PhysicalPlaquetteGraphRootShellSafeDeletionExists1296` were proved, it
would support `PhysicalPlaquetteGraphPortalSupportedSafeDeletionOrientation1296`
by choosing:

```text
deleted X = the root-shell safe deletion
parentOf X = root
portal residual = some root
essential residual = {root} when the residual fiber is nonempty, otherwise ∅
```

That bridge is intentionally not added, because the path pattern above shows
the proposed root-only portal policy is too strong in ordinary graph-theoretic
settings.

## Recommended Next Closure Path

Return to a flexible residual portal policy:

```text
PhysicalPlaquetteGraphFlexiblePortalSafeDeletionOrientation1296
```

The next scope should allow the portal and parent to depend on a residual-local
structure rather than forcing the parent to be the anchored root.  The key
requirement remains unchanged: the portal must be residual-only, and the
chosen-parent image over a residual fiber must lie in portal-local neighbor
shells with a `Fin 1296` code.

## Validation

Command:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result:

```text
Build completed successfully (8184 jobs).
```

No theorem proof was added.  No `sorry`; no new project axiom.

## Honesty Status

`F3-COUNT` remains `CONDITIONAL_BRIDGE`.  No ledger row, project percentage,
README metric, planner metric, or Clay-level claim moves from this scope task.
