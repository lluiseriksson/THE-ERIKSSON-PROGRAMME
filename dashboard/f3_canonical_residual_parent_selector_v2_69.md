# F3 B.2 v2.69 Canonical Residual Parent Selector Factoring

**Task**: `CODEX-F3-CANONICAL-RESIDUAL-PARENT-SELECTOR-001`
**Date**: 2026-04-26T17:20:00Z
**Status**: `NO_CLOSURE_SELECTOR_INTERFACE_LANDED`
**Ledger status**: `F3-COUNT` remains `CONDITIONAL_BRIDGE`.

## Target

The residual-parent invariant from v2.67 was factored into the exact
residual-only selector obligation:

```lean
PhysicalPlaquetteGraphCanonicalResidualParentSelector1296
```

The selector is required to depend only on the residual bucket:

```lean
Finset (ConcretePlaquette physicalClayDimension L) ->
  Option (ConcretePlaquette physicalClayDimension L)
```

It must not choose a parent post-hoc from the current `(X,z)` witness.

## Lean Interface Landed

Codex added:

```lean
PhysicalPlaquetteGraphCanonicalResidualParentSelector1296
physicalPlaquetteGraphResidualParentInvariant1296_of_canonicalResidualParentSelector1296
physicalPlaquetteGraphDeletedVertexDecoderStep1296_of_canonicalResidualParentSelector1296
```

This proves that the canonical selector is sufficient for the v2.67
residual-parent invariant and then for the v2.65 deleted-vertex decoder
contract.

## Validation

Build:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result: 8184/8184 jobs green.

Pinned traces:

```text
YangMills.physicalPlaquetteGraphResidualParentInvariant1296_of_canonicalResidualParentSelector1296
depends on axioms: [propext, Classical.choice, Quot.sound]

YangMills.physicalPlaquetteGraphDeletedVertexDecoderStep1296_of_canonicalResidualParentSelector1296
depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry`. No new project axiom.

## Exact Remaining Theorem

The remaining open theorem is:

```lean
PhysicalPlaquetteGraphCanonicalResidualParentSelector1296
```

It must define or prove a residual-only parent selector such that every
anchored bucket admits a safe deletion whose deleted plaquette is adjacent to
the selected residual parent.  The proof must not choose the parent from the
current deleted vertex after the residual is already fixed.

## Project Impact

This is a clean interface narrowing, not decoder closure.  `F3-COUNT` remains
`CONDITIONAL_BRIDGE`. No Clay-level, lattice-level, honest-discount, or
named-frontier percentage moves from this entry.
