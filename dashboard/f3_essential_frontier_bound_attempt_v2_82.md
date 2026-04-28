# F3 Essential Frontier Bound Attempt v2.82

Timestamp: 2026-04-27T08:15:00Z

Task: `CODEX-F3-PROVE-ESSENTIAL-FRONTIER-BOUND-001`

## Target

Attempted theorem:

```lean
PhysicalPlaquetteGraphEssentialSafeDeletionParentFrontierBound1296
```

This is the exact v2.81 open target behind the bridge:

```text
PhysicalPlaquetteGraphEssentialSafeDeletionParentFrontierBound1296
  -> PhysicalPlaquetteGraphResidualParentMenuBound1296
  -> PhysicalPlaquetteGraphResidualParentMenuCovers1296
  -> PhysicalPlaquetteGraphSymbolicResidualParentSelector1296
  -> PhysicalPlaquetteGraphDeletedVertexDecoderStep1296x1296
```

## Outcome

No proof was added. No counterexample was formalized.

The obstruction is now precise: one needs a canonical safe-deletion orientation
on anchored buckets whose residual fiber indegree, measured by chosen residual
parents, is uniformly bounded by `1296`.

Informally, for every current anchored bucket `X`, choose:

- a safe deleted plaquette `deleted X`,
- a parent `parentOf X ∈ X.erase (deleted X)`,
- with `deleted X` adjacent to `parentOf X`.

Then for each residual bucket `R`, the image

```lean
{ parentOf X | X.erase (deleted X) = R }
```

must have cardinality at most `1296`.

The existing local neighbor bound only controls, for a fixed parent `p`, how
many deleted plaquettes are adjacent to `p`. It does not control how many
parents may be needed across a residual fiber.

The v2.79 row-residual diagnostic shows why bounding the whole raw frontier is
the wrong theorem: raw one-step frontiers can grow with residual size.

## Why This Was Not Closed

The current Lean library has enough structure to state and bridge the target,
but not enough to construct the required canonical orientation.

A proof would require one of the following new mathematical ingredients:

1. A bounded-indegree safe-deletion orientation theorem for anchored plaquette
   animals.
2. A canonical deletion policy whose residual-fiber parent image is visibly
   local and bounded by the existing physical `1296` neighbor shell.
3. A proof that problematic raw-frontier growth patterns never force many
   essential parents because the canonical deletion can steer away from them.

None of these ingredients is currently present as a Lean theorem. Using
`Classical.choose` on safe deletions would choose post-hoc witnesses and would
not prove the residual-fiber image bound.

## Validation

Command:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result:

```text
Build completed successfully (8184 jobs).
```

No Lean file was changed by this attempt. No `sorry`. No new project axiom.

## Exact Next Theorem

The next useful theorem should isolate the missing orientation statement:

```lean
PhysicalPlaquetteGraphSafeDeletionOrientationIndegreeBound1296
```

Expected role:

```text
bounded-indegree safe-deletion orientation
  -> PhysicalPlaquetteGraphEssentialSafeDeletionParentFrontierBound1296
```

This theorem must not bound the raw residual frontier and must not use empirical
bounded search as proof.

## Status

`F3-COUNT` remains `CONDITIONAL_BRIDGE`.

The strengthened product-symbol route remains conditional and constants-audit
gated. No percentage, ledger status, or Clay claim moves from this attempt.
