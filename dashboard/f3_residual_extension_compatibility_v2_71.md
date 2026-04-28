# F3 B.2 v2.71 Residual-Extension Compatibility Interface

**Task**: `CODEX-F3-RESIDUAL-EXTENSION-COMPATIBILITY-001`
**Date**: 2026-04-26T17:40:00Z
**Status**: `INTERFACE_LANDED_COMPATIBILITY_OPEN`
**Ledger status**: `F3-COUNT` remains `CONDITIONAL_BRIDGE`.

## Target

v2.70 isolated the missing theorem behind:

```lean
PhysicalPlaquetteGraphCanonicalResidualParentSelector1296
```

The missing content is not local adjacency.  It is compatibility between a
parent chosen from the residual bucket alone and at least one safe deletion of
every current anchored bucket producing that residual.

## Lean Interface Landed

Codex added:

```lean
PhysicalPlaquetteGraphResidualExtensionCompatible1296
PhysicalPlaquetteGraphResidualExtensionCompatibility1296
physicalPlaquetteGraphCanonicalResidualParentSelector1296_of_residualExtensionCompatibility1296
```

The first definition says that a fixed residual-only parent selector works for
all current buckets at a fixed root/cardinality.  The second packages the
existence of such selectors for all physical roots/cardinalities.  The bridge
proves that this exact compatibility theorem implies the v2.69 canonical
selector.

## Validation

Build:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result: 8184/8184 jobs green.

Pinned trace:

```text
YangMills.physicalPlaquetteGraphCanonicalResidualParentSelector1296_of_residualExtensionCompatibility1296
depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry`. No new project axiom.

## Exact Remaining Theorem

The remaining theorem is:

```lean
PhysicalPlaquetteGraphResidualExtensionCompatibility1296
```

It must be proved without choosing the parent from the current `(X,z)` witness.
If false, the decoder symbol must be strengthened beyond the current
residual-plus-`Fin 1296` local-neighbor form.

## Project Impact

This is an interface narrowing, not decoder closure.  `F3-COUNT` remains
`CONDITIONAL_BRIDGE`.  No Clay-level, lattice-level, honest-discount,
named-frontier, README, or planner percentage moves from this entry.
