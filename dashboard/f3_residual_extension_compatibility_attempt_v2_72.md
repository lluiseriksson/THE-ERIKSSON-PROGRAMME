# F3 B.2 v2.72 Residual-Extension Compatibility Attempt

**Task**: `CODEX-F3-PROVE-RESIDUAL-EXTENSION-COMPATIBILITY-001`
**Date**: 2026-04-26T17:55:00Z
**Status**: `NO_CLOSURE_EQUIVALENT_TO_CANONICAL_SELECTOR`
**Ledger status**: `F3-COUNT` remains `CONDITIONAL_BRIDGE`.

## Target

The attempted theorem was:

```lean
PhysicalPlaquetteGraphResidualExtensionCompatibility1296
```

The theorem asks for a residual-only parent selector compatible with every
current anchored bucket.  The selector cannot be chosen from the current
`(X,z)` deletion witness.

## Lean Evidence Landed

Codex proved the reverse bridge and the equivalence:

```lean
physicalPlaquetteGraphResidualExtensionCompatibility1296_of_canonicalResidualParentSelector1296
physicalPlaquetteGraphResidualExtensionCompatibility1296_iff_canonicalResidualParentSelector1296
```

Together with v2.71, this shows that residual-extension compatibility is not a
new weaker theorem.  It is exactly the same mathematical content as:

```lean
PhysicalPlaquetteGraphCanonicalResidualParentSelector1296
```

## Why The Proof Did Not Close

The compatibility statement packages the same existential parent function as the
canonical selector.  Proving it would already prove the selector and hence feed
the v2.69/v2.67 bridges.  No independent residual-only construction was found.

This means the current proof route has reached an equivalence, not a descent:

```text
PhysicalPlaquetteGraphResidualExtensionCompatibility1296
  iff
PhysicalPlaquetteGraphCanonicalResidualParentSelector1296
```

## Exact Remaining Blocker

The remaining blocker is still a genuine residual-only construction:

```lean
PhysicalPlaquetteGraphCanonicalResidualParentSelector1296
```

Equivalently, prove `PhysicalPlaquetteGraphResidualExtensionCompatibility1296`.
The proof must define the parent from the residual bucket alone, then show that
every current bucket has at least one safe deletion compatible with that fixed
residual parent.

If this residual-only selector is false for the current symbol, the minimal next
design change is to strengthen the deleted-vertex symbol beyond the present
`residual bucket + Fin 1296 local-neighbor code`, for example by adding a
canonical residual-extension branch code or by changing the deletion rule so the
residual determines the admissible parent uniquely.

## Validation

Build:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result: 8184/8184 jobs green.

Pinned traces:

```text
YangMills.physicalPlaquetteGraphResidualExtensionCompatibility1296_of_canonicalResidualParentSelector1296
depends on axioms: [propext, Classical.choice, Quot.sound]

YangMills.physicalPlaquetteGraphResidualExtensionCompatibility1296_iff_canonicalResidualParentSelector1296
depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry`. No new project axiom.

## Project Impact

This is a no-closure/equivalence entry, not decoder closure. `F3-COUNT` remains
`CONDITIONAL_BRIDGE`. No Clay-level, lattice-level, honest-discount,
named-frontier, README, or planner percentage moves from this entry.
