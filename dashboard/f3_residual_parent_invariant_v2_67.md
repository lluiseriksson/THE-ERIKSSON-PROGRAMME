# F3 B.2 v2.67 Residual Parent Invariant Interface

**Task**: `CODEX-F3-RESIDUAL-PARENT-INVARIANT-001`
**Date**: 2026-04-26T16:55:00Z
**Status**: interface and bridge landed; invariant theorem remains open.
**Ledger status**: `F3-COUNT` remains `CONDITIONAL_BRIDGE`.

## Lean Artifacts Added

Codex added the local finite inverse:

```lean
physicalNeighborDecodeOfStepCode
physicalNeighborDecodeOfStepCode_spec
```

The inverse is only local to one selected residual parent. It inverts a
neighbor-code on the actual `neighborFinset` using the existing injectivity
shape:

```lean
Set.InjOn (code p)
  {q | q ∈ (plaquetteGraph physicalClayDimension L).neighborFinset p}
```

Codex also added the canonical residual-parent/frontier interface:

```lean
PhysicalPlaquetteGraphResidualParentInvariant1296
```

and the bridge:

```lean
physicalPlaquetteGraphDeletedVertexDecoderStep1296_of_residualParentInvariant1296
```

The bridge proves that once the residual-parent invariant is available, the
named v2.65 contract follows:

```lean
PhysicalPlaquetteGraphDeletedVertexDecoderStep1296
```

## Validation

Build:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result: 8184/8184 jobs green.

Pinned traces:

```text
YangMills.physicalNeighborDecodeOfStepCode_spec
depends on axioms: [propext, Classical.choice, Quot.sound]

YangMills.physicalPlaquetteGraphDeletedVertexDecoderStep1296_of_residualParentInvariant1296
depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry`. No project axiom. No existential-only deleted-vertex decoder.

## Exact Blocker

The following proposition is now the precise remaining theorem:

```lean
PhysicalPlaquetteGraphResidualParentInvariant1296
```

It must supply, uniformly in each physical anchored bucket, a residual parent
selected from `X.erase z` such that an admissible deleted plaquette `z` is in
the selected parent's plaquette-graph `neighborFinset`. That reduces the
deleted-vertex reconstruction to a single `Fin 1296` local-neighbor symbol.

## Project Impact

This is a real narrowing of the B.2 interface, but not a closure of F3-COUNT.
`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No Clay-level, lattice-level,
honest-discount, or named-frontier percentage moves from this entry.
