# F3 B.2 v2.66 Reconstructive Contract Attempt

**Task**: `CODEX-F3-RECONSTRUCTIVE-CONTRACT-PROOF-001`  
**Date**: 2026-04-26T16:40:22Z  
**Status**: `NO_CLOSURE` / stop condition reached.  
**Ledger status**: `F3-COUNT` remains `CONDITIONAL_BRIDGE`.

## Target

The attempted target was:

```lean
PhysicalPlaquetteGraphDeletedVertexDecoderStep1296
```

This asks for, for each physical root and cardinality `k`, one global
reconstruction function:

```lean
Finset (ConcretePlaquette physicalClayDimension L) ->
  Fin 1296 ->
    Option (ConcretePlaquette physicalClayDimension L)
```

such that every nontrivial anchored bucket has at least one safe deleted
plaquette recoverable from `(X.erase z, symbol)`.

## What is already available

Lean already proves the safe-deletion existence:

```lean
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem
```

and the module builds:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result: build passed.

The relevant existing projector remains oracle-clean:

```text
YangMills.physicalPlaquetteGraphDeletedVertexDecoderStep1296_exists_recoverable_deletion
depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Why the contract did not close

The safe-deletion theorem gives, for each bucket `X`, some non-root deleted
plaquette `z` such that `X.erase z` is still anchored and preconnected.  It
does **not** provide a canonical way to recover `z` from the residual bucket
alone plus one local `Fin 1296` symbol.

The obvious reconstruction idea is:

1. take the residual bucket `R = X.erase z`;
2. use the symbol to choose a neighbor of some parent in `R`;
3. recover `z`.

The missing piece is the parent.  A deleted plaquette is adjacent to some
member of the residual bucket, but current Lean facts do not identify a
canonical parent in the residual.  Without such a parent, the set of possible
extensions of a residual bucket is bounded only by roughly
`1296 * R.card`, not by `1296` uniformly.

Equivalently, the current symbol is local-neighbor sized, while the residual
extension problem is residual-boundary sized.  A proof using
`Classical.choose` to select a deleted vertex would be existential-only and
would fail the audit requirement.

## Exact Remaining Theorem

One of the following must be proved before the v2.65 contract can close:

```lean
-- Preferred shape:
-- for every residual bucket R arising from safe deletion, there is a canonical
-- parent p(R) in R such that at least one valid deleted vertex z is adjacent to
-- p(R), making z recoverable from the existing Fin 1296 neighbor code.
```

or:

```lean
-- Alternative shape:
-- for every residual bucket R, the valid deleted-vertex extensions of R that
-- occur in anchored buckets of cardinality k admit an injection into Fin 1296.
```

The second statement is likely false without an additional canonical-parent
or frontier-minimality invariant, because residual boundary size can grow with
`R.card`.

## Recommendation

Exactly one next closure path is recommended:

**Define a canonical residual parent/frontier invariant** for the deletion
step, then prove that the selected deleted vertex lies in the `neighborFinset`
of that parent.  After that, the existing `Fin 1296` neighbor-code machinery
can be used honestly.

Do not attempt to close `PhysicalPlaquetteGraphDeletedVertexDecoderStep1296`
with an existential-only `Classical.choose` decoder.  That would not be a
reconstructive finite-alphabet decoder.

## Project Impact

No Lean theorem was added.  No project axiom or `sorry` was introduced.
`F3-COUNT` remains `CONDITIONAL_BRIDGE`.  No Clay-level, lattice-level, or
named-frontier percentage moved.
