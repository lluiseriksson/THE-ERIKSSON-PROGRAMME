# F3 Safe-Deletion Orientation-Code Bound Attempt v2.85

Timestamp: 2026-04-27T09:00:00Z

Task: `CODEX-F3-PROVE-SAFE-DELETION-ORIENTATION-CODE-BOUND-001`

## Target

Attempted target:

```lean
PhysicalPlaquetteGraphSafeDeletionOrientationCodeBound1296
```

This is the v2.84 open theorem behind the bridge:

```text
PhysicalPlaquetteGraphSafeDeletionOrientationCodeBound1296
  -> PhysicalPlaquetteGraphEssentialSafeDeletionParentFrontierBound1296
  -> PhysicalPlaquetteGraphResidualParentMenuBound1296
  -> PhysicalPlaquetteGraphResidualParentMenuCovers1296
  -> PhysicalPlaquetteGraphSymbolicResidualParentSelector1296
  -> PhysicalPlaquetteGraphDeletedVertexDecoderStep1296x1296
```

## Outcome

No proof was added.

The repository currently proves:

- existence of safe deleted plaquettes for anchored buckets;
- existence of a residual neighbor parent once a deleted plaquette is given;
- local `Fin 1296` coding for neighbors of one fixed parent;
- the v2.84 bridge from an injective residual-indexed orientation code to the
  essential frontier bound.

What is still missing is the new mathematical construction:

```text
choose deleted X and parentOf X canonically for every current bucket X
so that, for each residual R, the chosen-parent menu over the fiber
  {X | X.erase (deleted X) = R}
injects into Fin 1296.
```

Using `Classical.choose` on existing safe-deletion existence theorems would only
select post-hoc witnesses.  It would not produce the residual-fiber injectivity
or the uniform `Fin 1296` code required by
`PhysicalPlaquetteGraphSafeDeletionOrientationCodeBound1296`.

## Precise Blocker

The exact remaining theorem is a constructive canonical orientation policy:

```lean
PhysicalPlaquetteGraphSafeDeletionOrientationCodeBound1296
```

More concretely, one must construct:

```lean
deleted   : Finset (ConcretePlaquette physicalClayDimension L)
              -> ConcretePlaquette physicalClayDimension L
parentOf  : Finset (ConcretePlaquette physicalClayDimension L)
              -> ConcretePlaquette physicalClayDimension L
essential : Finset (ConcretePlaquette physicalClayDimension L)
              -> Finset (ConcretePlaquette physicalClayDimension L)
orientCode :
  ∀ residual,
    {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual}
      -> Fin 1296
```

with `Function.Injective (orientCode residual)` for every residual and with the
safe-deletion/neighbor-parent clauses.  The existing local neighbor code cannot
be lifted to this statement without first proving that the chosen-parent image
inside each residual fiber is itself uniformly codeable.

## Non-Routes Ruled Out

- **Raw residual frontier bound**: v2.79 already shows raw residual frontier
  growth is the wrong object.
- **Fixed-parent local degree bound**: `neighborFinset` degree `≤ 1296` controls
  deleted plaquettes adjacent to one parent, not the number of parents needed
  across a residual fiber.
- **Existential safe-deletion choice**: `Classical.choose` supplies witnesses but
  no residual-fiber injection.
- **Empirical bounded search**: useful as diagnostic input only; it cannot prove
  the Lean theorem.

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

## Recommended Next Task

```text
CODEX-F3-SAFE-DELETION-ORIENTATION-POLICY-SCOPE-001
```

Scope a concrete canonical orientation policy, for example based on a
residual-local boundary order or root-directed traversal, and state the smallest
Lean lemma that would imply
`PhysicalPlaquetteGraphSafeDeletionOrientationCodeBound1296` without bounding
the raw frontier.

## Honesty Status

`F3-COUNT` remains `CONDITIONAL_BRIDGE`.  The strengthened product-symbol route
remains conditional and constants-audit gated.  No status, percentage, README
metric, planner metric, or Clay-level claim moves from this attempt.
