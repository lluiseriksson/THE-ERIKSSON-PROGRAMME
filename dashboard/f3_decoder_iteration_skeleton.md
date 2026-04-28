# F3 B.2 Anchored Word Decoder Iteration Skeleton

**Task**: `CODEX-F3-DECODER-ITERATION-SKELETON-001`  
**Date**: 2026-04-26T16:24:00Z  
**Status**: planning skeleton complete; no Lean theorem added.  
**Ledger status**: `F3-COUNT` remains `CONDITIONAL_BRIDGE`.

## Scope

This file is the implementation skeleton that should consume the v2.65 contract:

```lean
PhysicalPlaquetteGraphDeletedVertexDecoderStep1296
```

It does not prove that contract and does not prove the anchored decoder. It fixes the shape of the next implementation pass so Codex does not re-derive the B.2 API surface.

## Induction Measure

Use the anchored bucket index/cardinality `k` in:

```lean
plaquetteGraphPreconnectedSubsetsAnchoredCard
  physicalClayDimension L root k
```

The nontrivial target is the `1 < k` input consumed by:

```lean
physicalPlaquetteGraphAnimalAnchoredWordDecoderBound1296_of_nontrivial
```

The final anchored decoder target is:

```lean
PhysicalPlaquetteGraphAnimalAnchoredWordDecoderBound 1296
```

Base cases `k <= 1` are already handled by:

```lean
plaquetteGraphPreconnectedSubsetsAnchoredCard_base_wordDecoderCovers
PhysicalPlaquetteGraphAnimalAnchoredWordDecoderBound.of_nontrivial
```

## Residual Term

The residual bucket at a nontrivial step is:

```lean
X.erase z
```

where `z` is a non-root deleted plaquette and:

```lean
X.erase z ∈
  plaquetteGraphPreconnectedSubsetsAnchoredCard
    physicalClayDimension L root (k - 1)
```

Current unconditional existence of a safe residual is supplied by:

```lean
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem
```

Current recoverable residual is supplied only conditionally by:

```lean
physicalPlaquetteGraphDeletedVertexDecoderStep1296_exists_recoverable_deletion
```

using the still-open contract:

```lean
PhysicalPlaquetteGraphDeletedVertexDecoderStep1296
```

## Code Alphabet

The code alphabet remains:

```lean
Fin 1296
```

Do not introduce a larger alphabet unless the v2.65 contract is proved impossible at `1296`. The intended single-step symbol is exactly the `symbol : Fin 1296` in the v2.65 contract, not merely an unverified `Classical.choose` witness.

## Word Shape

The existing anchored decoder target uses:

```lean
(Fin k → Fin 1296) → Finset (ConcretePlaquette physicalClayDimension L)
```

The implementation pass should use the existing word shape directly. If a cons-style helper is needed, introduce it only as a local helper around `Fin k → Fin 1296`; avoid a new project-level word type unless Lean ergonomics force it.

Candidate local helper names:

```lean
physicalPlaquetteGraphAnimalAnchoredDecoder_cons
physicalPlaquetteGraphAnimalAnchoredDecoder_residual_cons_covers
```

These helpers should be attempted only after the v2.65 reconstruction contract is usable, because the cons step must rebuild `X` from `X.erase z` and the recovered `z`.

## Handoff Theorem Sequence

The clean implementation order is:

1. Prove the v2.65 reconstruction contract:

```lean
theorem physicalPlaquetteGraphDeletedVertexDecoderStep1296 :
    PhysicalPlaquetteGraphDeletedVertexDecoderStep1296
```

Recommended actual theorem name to avoid colliding with the `def`:

```lean
theorem physicalPlaquetteGraphDeletedVertexDecoderStep1296_proved :
    PhysicalPlaquetteGraphDeletedVertexDecoderStep1296
```

2. Prove the nontrivial anchored decoder step:

```lean
theorem physicalPlaquetteGraphAnimalAnchoredWordDecoderBound1296_nontrivial_step
    {L k : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L)
    (hk : 1 < k) :
    ∃ decode : (Fin k → Fin 1296) →
        Finset (ConcretePlaquette physicalClayDimension L),
      ∀ X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root k,
        ∃ word : Fin k → Fin 1296, decode word = X
```

3. Package the full anchored decoder:

```lean
theorem physicalPlaquetteGraphAnimalAnchoredWordDecoderBound1296 :
    PhysicalPlaquetteGraphAnimalAnchoredWordDecoderBound 1296
```

using:

```lean
physicalPlaquetteGraphAnimalAnchoredWordDecoderBound1296_of_nontrivial
```

4. Bridge anchored buckets to the connecting-cluster baseline target:

```lean
theorem physicalConnectingClusterBaselineExtraWordDecoderCovers1296_of_anchored :
    PhysicalPlaquetteGraphAnimalAnchoredWordDecoderBound 1296 →
      PhysicalConnectingClusterBaselineExtraWordDecoderCovers1296
```

This bridge may already be mostly covered by the graph-animal count/connecting-cluster bridge near the existing shifted count package. If it is not present, it is a separate Codex task and F3-COUNT remains conditional.

5. Close the B.2 consumer:

```lean
theorem physicalConnectingClusterBaselineExtraWordDecoderCovers1296_proved :
    PhysicalConnectingClusterBaselineExtraWordDecoderCovers1296
```

6. Only after Cowork audit, package the F3 count:

```lean
def physicalShiftedF3CountPackageExp_via_B2 :
    PhysicalShiftedF3CountPackageExp :=
  physicalShiftedF3CountPackageExp_of_baselineExtraWordDecoderCovers1296
    physicalConnectingClusterBaselineExtraWordDecoderCovers1296_proved
```

## Stop Point For The Next Coding Pass

The next coding pass should stop if it cannot prove:

```lean
PhysicalPlaquetteGraphDeletedVertexDecoderStep1296
```

without `sorry` or a new project axiom. A partial decoder that merely chooses deleted vertices existentially is not enough, because the decoder must reconstruct the original bucket from `(residual bucket, symbol : Fin 1296)`.

## Validation Notes

No Lean file was edited by this skeleton task, so no `lake build` was required here. The required skeleton components are named above:

- induction measure: anchored bucket index/cardinality `k`
- residual term: `X.erase z`
- code alphabet: `Fin 1296`
- final decoder theorem: `physicalConnectingClusterBaselineExtraWordDecoderCovers1296_proved`

No mathematical status row and no project percentage changed.
