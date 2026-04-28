# F3 B.2 Reconstructive Deleted-Vertex Symbol

**Task**: `CODEX-F3-RECONSTRUCTIVE-DECODER-SYMBOL-001`  
**Date**: 2026-04-26T16:12:02Z  
**Status**: `DONE` for the narrow interface task; `F3-COUNT` remains `CONDITIONAL_BRIDGE`.

## Lean identifiers landed

File: `YangMills/ClayCore/LatticeAnimalCount.lean`

- `PhysicalPlaquetteGraphDeletedVertexDecoderStep1296`
- `physicalPlaquetteGraphDeletedVertexDecoderStep1296_exists_recoverable_deletion`

The definition is a `Prop` contract for the B.2 one-step decoder: for every physical root and cardinality `k`, a single reconstruction function

```lean
Finset (ConcretePlaquette physicalClayDimension L) -> Fin 1296 ->
  Option (ConcretePlaquette physicalClayDimension L)
```

must recover the deleted non-root plaquette from the residual bucket plus one `Fin 1296` symbol for every nontrivial anchored bucket.

The theorem is intentionally only a projector from that contract. It extracts a recoverable safe deletion if the contract is already available. It does not prove the contract.

## Validation

Command:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result: build passed.

Pinned trace:

```text
'YangMills.physicalPlaquetteGraphDeletedVertexDecoderStep1296_exists_recoverable_deletion'
depends on axioms: [propext, Classical.choice, Quot.sound]
```

No new project axiom was introduced. No `sorry` was introduced.

## Remaining blocker

The exact open theorem is now:

```lean
PhysicalPlaquetteGraphDeletedVertexDecoderStep1296
```

The next closure task must construct a uniform `reconstruct` function and prove that, for every nontrivial anchored physical bucket `X`, at least one safe deleted plaquette `z` can be recovered from `(X.erase z, symbol : Fin 1296)`.

The existing root-shell / parent-code artifacts identify branches and witnesses, but they do not yet prove this reconstruction from residual data plus a finite symbol. That injective reconstruction proof is still the B.2 mathematical content.

## Ledger discipline

`UNCONDITIONALITY_LEDGER.md` keeps `F3-COUNT` as `CONDITIONAL_BRIDGE`. No lattice percentage, Clay-as-stated percentage, or planner percentage moved from this task.

## Recommendation

Exactly one next closure path is recommended:

**In-project proof** of `PhysicalPlaquetteGraphDeletedVertexDecoderStep1296`, using the v2.64 residual handoff plus a finite deleted-vertex symbol that is verified to reconstruct the deleted plaquette from the residual bucket.
