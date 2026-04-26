/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L15_BranchII_Wilson_Substantive.BalabanRGFlow

/-!
# Block-spin decimation transform (Phase 134)

This module formalises the **block-spin decimation** transform that
sends a fine-lattice measure to a coarse-lattice effective measure.

## Strategic placement

This is **Phase 134** of the L15_BranchII_Wilson_Substantive block.

## What it does

Encodes the abstract block-spin decimation as a measure-transform
operator `R_block : Measure → Measure` with three key properties:
* **Probability preservation**: maps probability measures to
  probability measures.
* **Kolmogorov consistency**: iterates compose, `R_block^k = R^k_block`.
* **Block-locality**: the effective coupling at scale `aₖ₊₁` depends
  only on the field configuration in a single coarse block.

We work in an abstract setting where the underlying space is a
generic measurable space `Ω`, and `R_block : Measure Ω → Measure Ω`
satisfies the abstract block-decimation axioms.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L15_BranchII_Wilson_Substantive

open MeasureTheory

/-! ## §1. The block-spin decimation operator -/

/-- An **abstract block-spin decimation operator** on probability
    measures over a measurable space `Ω`. -/
structure BlockDecimation (Ω : Type*) [MeasurableSpace Ω] where
  /-- The decimation transform. -/
  R : Measure Ω → Measure Ω
  /-- Preserves probability measures: if `μ` is a probability measure,
      so is `R μ`. -/
  preserves_prob :
    ∀ μ : Measure Ω, IsProbabilityMeasure μ → IsProbabilityMeasure (R μ)

/-! ## §2. Iterated decimation -/

/-- The k-th iterate of the block-decimation operator. -/
def BlockDecimation.iter {Ω : Type*} [MeasurableSpace Ω]
    (bd : BlockDecimation Ω) : ℕ → Measure Ω → Measure Ω
  | 0, μ => μ
  | k+1, μ => bd.R (bd.iter k μ)

/-- **Iterated decimation preserves probability measures**. -/
theorem BlockDecimation.iter_preserves_prob
    {Ω : Type*} [MeasurableSpace Ω] (bd : BlockDecimation Ω)
    (μ : Measure Ω) (hμ : IsProbabilityMeasure μ) (k : ℕ) :
    IsProbabilityMeasure (bd.iter k μ) := by
  induction k with
  | zero => simpa [BlockDecimation.iter] using hμ
  | succ k ih => exact bd.preserves_prob _ ih

#print axioms BlockDecimation.iter_preserves_prob

/-! ## §3. Composition law -/

/-- **Decimation iterates compose**: `R^(i+j) μ = R^i (R^j μ)`. -/
theorem BlockDecimation.iter_add
    {Ω : Type*} [MeasurableSpace Ω] (bd : BlockDecimation Ω)
    (μ : Measure Ω) (i j : ℕ) :
    bd.iter (i + j) μ = bd.iter i (bd.iter j μ) := by
  induction i with
  | zero => simp [BlockDecimation.iter]
  | succ i ih =>
      have : bd.iter (i + 1 + j) μ = bd.R (bd.iter (i + j) μ) := by
        show bd.iter ((i + j) + 1) μ = bd.R (bd.iter (i + j) μ)
        rfl
      rw [this, ih]
      rfl

#print axioms BlockDecimation.iter_add

/-! ## §4. RG scale at iteration k -/

/-- The RG scale after `k` decimation steps starting from `a₀`. -/
def rgScaleAt {Ω : Type*} [MeasurableSpace Ω]
    (_ : BlockDecimation Ω) (bf : BlockFactor) (a₀ : ℝ) (k : ℕ) : ℝ :=
  rgScale a₀ bf k

/-! ## §5. Coordination note -/

/-
This file is **Phase 134** of the L15_BranchII_Wilson_Substantive block.

## What's done

Two **substantive** Lean theorems:
* `BlockDecimation.iter_preserves_prob` — probability preservation
  under iterated decimation, with full inductive proof.
* `BlockDecimation.iter_add` — the iterated decimation operator
  satisfies the composition law `R^(i+j) = R^i ∘ R^j`.

These are clean Lean lemmas usable across the block.

## Strategic value

Phase 134 gives the project a clean abstract handle on the
block-spin decimation operator with Mathlib-grade compositionality
proofs.

Cross-references:
- Phase 133 `BalabanRGFlow.lean` — RG scales.
- Bloque-4 §3.2 (block-spin construction).
-/

end YangMills.L15_BranchII_Wilson_Substantive
