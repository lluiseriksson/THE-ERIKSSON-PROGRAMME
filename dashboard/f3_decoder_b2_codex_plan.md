# F3 B.2 Codex Implementation Plan

Generated: 2026-04-26T15:35Z  
Task: `CODEX-F3-DECODER-B2-PREP-001`  
Status: Codex-ready plan only; no Lean theorem added.

## Honesty Status

This plan does not prove B.2 and does not close F3-COUNT.  It translates the
Cowork B.2 scope into a current v2.63 implementation checklist tied to live
Lean identifiers.  `F3-COUNT` remains `CONDITIONAL_BRIDGE`; no planner or
README percentage may move from this preparatory artifact.

## Current State After v2.63

B.1 is no longer the blocker.  The live file now contains oracle-clean exact
safe deletion:

```lean
theorem plaquetteGraphAnchoredSafeDeletionExists
    {d L : ℕ} [NeZero d] [NeZero L] :
    PlaquetteGraphAnchoredSafeDeletionExists d L

theorem physicalPlaquetteGraphAnchoredSafeDeletionExists
    {L : ℕ} [NeZero L] :
    PhysicalPlaquetteGraphAnchoredSafeDeletionExists L
```

Live references:

- `YangMills/ClayCore/LatticeAnimalCount.lean:2578`
- `YangMills/ClayCore/LatticeAnimalCount.lean:2585`

The remaining B.2 target is still:

```lean
theorem physicalConnectingClusterBaselineExtraWordDecoderCovers1296_proved :
    PhysicalConnectingClusterBaselineExtraWordDecoderCovers1296
```

Live target/consumer references:

- `PhysicalConnectingClusterBaselineExtraWordDecoderCovers`: `LatticeAnimalCount.lean:1057`
- `PhysicalConnectingClusterBaselineExtraWordDecoderCovers1296`: `LatticeAnimalCount.lean:1084`
- `physicalShiftedF3CountPackageExp_of_baselineExtraWordDecoderCovers1296`: `LatticeAnimalCount.lean:1096`

## Induction Measure

Use the anchored bucket cardinality `k` as the primary induction measure for
the anchored decoder:

```lean
PhysicalPlaquetteGraphAnimalAnchoredWordDecoderBound 1296
```

Live target:

- `PhysicalPlaquetteGraphAnimalAnchoredWordDecoderBound`: `LatticeAnimalCount.lean:3013`

The natural helper theorem should be the nontrivial-step constructor consumed
by the existing bridge:

```lean
theorem physicalPlaquetteGraphAnimalAnchoredWordDecoderBound1296_nontrivial_step
    {L k : ℕ} [NeZero L]
    {root : ConcretePlaquette physicalClayDimension L}
    (hk : 2 ≤ k)
    (hrec : ∀ j < k,
      ∃ decode : (Fin j → Fin 1296) →
          Finset (ConcretePlaquette physicalClayDimension L),
        ∀ X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root j,
          ∃ word : Fin j → Fin 1296, decode word = X) :
    ∃ decode : (Fin k → Fin 1296) →
        Finset (ConcretePlaquette physicalClayDimension L),
      ∀ X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root k,
        ∃ word : Fin k → Fin 1296, decode word = X
```

This statement is deliberately local to anchored buckets.  Once proved, it
should feed:

```lean
PhysicalPlaquetteGraphAnimalAnchoredWordDecoderBound.of_nontrivial
```

Live references:

- base dispatcher: `plaquetteGraphPreconnectedSubsetsAnchoredCard_base_wordDecoderCovers`
  at `LatticeAnimalCount.lean:2957`
- existing nontrivial packaging surface:
  `PhysicalPlaquetteGraphAnimalAnchoredWordDecoderBound.of_nontrivial`
  at `LatticeAnimalCount.lean:3024`

## Residual Bucket Term

The residual at each step is the erased bucket supplied by exact safe deletion,
not the older `firstDeleteResidual1296` primitive unless Codex chooses to
reuse the legacy selector.

Preferred live handoff:

```lean
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem_of_safeDeletion
    (hsafe := physicalPlaquetteGraphAnchoredSafeDeletionExists)
```

Live reference:

- `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem_of_safeDeletion`
  at `LatticeAnimalCount.lean:2148`

For `X ∈ anchored root k` and `2 ≤ k`, obtain:

```lean
∃ z, ∃ hzX : z ∈ X, z ≠ root ∧
  X.erase z ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
    physicalClayDimension L root (k - 1)
```

The recursive call is on `X.erase z`, whose bucket index is `k - 1`.  The
strict decrease is therefore the index decrease `k - 1 < k`, discharged by
`omega` from `2 ≤ k`.

Legacy residual primitives still useful for cross-checking and possible reuse:

- `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_firstDeleteResidual1296`
  at `LatticeAnimalCount.lean:1604`
- `_firstDeleteResidual1296_card` at `LatticeAnimalCount.lean:1618`
- `_root_mem_firstDeleteResidual1296` at `LatticeAnimalCount.lean:1637`
- `_firstDeleteResidual1296_mem_of_preconnected` at `LatticeAnimalCount.lean:1690`

## Code Alphabet

The B.2 decoder uses the existing physical alphabet:

```lean
Fin 1296
```

Do not introduce a new alphabet unless a proof attempt shows the existing
parent code cannot express the reconstruction step.

Symbol source:

- `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParentCode1296`
  at `LatticeAnimalCount.lean:2742`
- `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParentCode1296_spec`
  at `LatticeAnimalCount.lean:2794`

Important caveat: the existing parent code takes a member of the current
bucket and returns a root-shell parent symbol.  In B.2, Codex must verify that
the chosen deleted vertex `z` can be reconstructed from the residual plus this
symbol.  This is the genuine decoder-content point; merely selecting a `z`
with `Classical.choose` is not enough for an injective decoder.

## Handoff Theorem Names

Recommended theorem order for the next implementation pass:

1. `physicalPlaquetteGraphAnimalAnchoredWordDecoderBound1296_nontrivial_step`
   - local nontrivial step for anchored buckets.
   - consumes `physicalPlaquetteGraphAnchoredSafeDeletionExists`.
   - produces a decoder for size `k`.

2. `physicalPlaquetteGraphAnimalAnchoredWordDecoderBound1296`
   - full anchored decoder:
     ```lean
     theorem physicalPlaquetteGraphAnimalAnchoredWordDecoderBound1296 :
         PhysicalPlaquetteGraphAnimalAnchoredWordDecoderBound 1296
     ```
   - uses base case at `LatticeAnimalCount.lean:2957` and the nontrivial step.

3. `physicalConnectingClusterBaselineExtraWordDecoderCovers1296_of_anchored`
   - bridges anchored animal decoder to connecting-cluster baseline decoder.
   - likely consumes existing graph-animal shifted/anchored bridges around
     `LatticeAnimalCount.lean:3067-3637`.

4. `physicalConnectingClusterBaselineExtraWordDecoderCovers1296_proved`
   - final B.2 target:
     ```lean
     theorem physicalConnectingClusterBaselineExtraWordDecoderCovers1296_proved :
         PhysicalConnectingClusterBaselineExtraWordDecoderCovers1296
     ```

5. `physicalShiftedF3CountPackageExp_via_B2`
   - optional packaging theorem:
     ```lean
     def physicalShiftedF3CountPackageExp_via_B2 :
         PhysicalShiftedF3CountPackageExp :=
       physicalShiftedF3CountPackageExp_of_baselineExtraWordDecoderCovers1296
         physicalConnectingClusterBaselineExtraWordDecoderCovers1296_proved
     ```
   - do not add this until Cowork audits the B.2 proof chain.

## First Lean Pass Checklist

1. Inspect `PhysicalPlaquetteGraphAnimalAnchoredWordDecoderBound.of_nontrivial`.
   Decide whether it already supplies the exact induction principle or whether
   a new `Nat.strong_induction_on` wrapper is cleaner.

2. Prove only a local reconstruction lemma first:

   ```lean
   -- candidate name
   theorem physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_decoder_step_covers
   ```

   It should state that if the residual decoder covers `X.erase z`, then a
   `Fin.cons symbol residualWord` covers `X`.

3. Use `Fin.cons` for word extension.  Avoid custom word types until Mathlib
   or Lean ergonomics force one.

4. Validate reconstruction, not only existence:
   the step must show the decoder output equals the original `X`, not just
   some bucket of the same cardinality.

5. Add `#print axioms` only after a theorem lands.  Expected trace ceiling:
   `[propext, Classical.choice, Quot.sound]`.

## Stop Conditions For Next Pass

- If the parent symbol does not reconstruct the deleted vertex from the
  residual, stop and file a narrower task for a reconstruction/injectivity
  lemma.
- If a proof requires a new project axiom or `sorry`, stop.
- If the anchored decoder can be shown but the connecting-cluster baseline
  bridge is missing, keep F3-COUNT `CONDITIONAL_BRIDGE` and create a bridge
  task rather than claiming closure.
- Do not move any progress percentage until B.2 and Cowork audit both land.

## Validation For This Prep Task

- This file identifies the induction measure: anchored bucket index/cardinality
  `k`.
- This file identifies the residual bucket term: `X.erase z` supplied by
  `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem_of_safeDeletion`.
- This file identifies the code alphabet: `Fin 1296`.
- This file names the handoff theorem sequence above.
- No Lean file was edited, so no `lake build` was required for this prep task.
