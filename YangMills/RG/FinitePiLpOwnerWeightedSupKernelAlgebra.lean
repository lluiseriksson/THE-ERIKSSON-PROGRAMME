/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.FinitePiLpOwnerWeightedSupKernel

/-!
# PRE-VALIDATION: algebra of output-fixed weighted owner rows

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been compiler-verified.

The coefficient matrix between complete owner fibres composes by literal
matrix convolution.  The output-fixed weighted row is submultiplicative at
the same rate whenever the owner distance satisfies the triangle inequality.

This is finite norm algebra.  It introduces no coordinate probes, owner
cardinality, physical constant, contraction hypothesis, or Neumann inverse.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

/-- Literal convolution of two owner-block coefficient matrices. -/
noncomputable def finiteOwnerKernelConvolution
    {β : Type*} [Fintype β]
    (left right : β → β → ℝ) (targetBlock sourceBlock : β) : ℝ :=
  ∑ middleBlock : β,
    left targetBlock middleBlock * right middleBlock sourceBlock

/-- The finite supremum norm of a finite sum is at most the sum of the
individual finite supremum norms. -/
theorem finitePiLpSupNorm_sum_le
    {n ι g : Type*} [Fintype n] [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup g]
    (f : n → FinitePiLpField ι g) :
    finitePiLpSupNorm (∑ j, f j) ≤ ∑ j, finitePiLpSupNorm (f j) := by
  apply finitePiLpSupNorm_le_of_norm_apply_le
  intro i
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  calc
    ‖∑ j, f j i‖ ≤ ∑ j, ‖f j i‖ := norm_sum_le _ _
    _ ≤ ∑ j, finitePiLpSupNorm (f j) := by
      apply Finset.sum_le_sum
      intro j _hj
      exact norm_apply_le_finitePiLpSupNorm (f j) i

/-- Exact owner projection commutes with a finite sum. -/
theorem finitePiLpOwnerPart_sum
    {n ι β g : Type*} [Fintype n] [Fintype ι] [DecidableEq β]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (ownerMap : ι → β) (owner : β)
    (f : n → FinitePiLpField ι g) :
    finitePiLpOwnerPart ownerMap owner (∑ j, f j) =
      ∑ j, finitePiLpOwnerPart ownerMap owner (f j) := by
  unfold finitePiLpOwnerPart
  rw [map_sum]

/-- Owner-block action bounds compose by literal convolution of their
nonnegative scalar coefficient matrices. -/
theorem finitePiLpTypedOwnerSupKernelBound_comp
    {ι κ ν β g : Type*}
    [Fintype ι] [Nonempty ι]
    [Fintype κ] [Nonempty κ]
    [Fintype ν] [Nonempty ν]
    [Fintype β] [DecidableEq β]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    {Left : FinitePiLpField κ g →L[ℝ] FinitePiLpField ν g}
    {Right : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g}
    {sourceOwner : ι → β} {middleOwner : κ → β} {targetOwner : ν → β}
    {leftCoefficient rightCoefficient : β → β → ℝ}
    (hLeft : FinitePiLpTypedOwnerSupKernelBound
      Left middleOwner targetOwner leftCoefficient)
    (hRight : FinitePiLpTypedOwnerSupKernelBound
      Right sourceOwner middleOwner rightCoefficient) :
    FinitePiLpTypedOwnerSupKernelBound
      (Left.comp Right) sourceOwner targetOwner
      (finiteOwnerKernelConvolution leftCoefficient rightCoefficient) := by
  classical
  refine ⟨?_, ?_⟩
  · intro targetBlock sourceBlock
    unfold finiteOwnerKernelConvolution
    exact Finset.sum_nonneg fun middleBlock _ =>
      mul_nonneg (hLeft.1 targetBlock middleBlock)
        (hRight.1 middleBlock sourceBlock)
  · intro sourceBlock f hf targetBlock
    have hdecomp : Right f =
        ∑ middleBlock,
          finitePiLpOwnerPart middleOwner middleBlock (Right f) :=
      (sum_finitePiLpOwnerPart_eq middleOwner (Right f)).symm
    have htargetDecomp :
        finitePiLpOwnerPart targetOwner targetBlock ((Left.comp Right) f) =
          ∑ middleBlock,
            finitePiLpOwnerPart targetOwner targetBlock
              (Left (finitePiLpOwnerPart middleOwner middleBlock (Right f))) := by
      rw [ContinuousLinearMap.comp_apply, hdecomp, map_sum,
        finitePiLpOwnerPart_sum]
    rw [htargetDecomp]
    calc
      finitePiLpSupNorm
          (∑ middleBlock,
            finitePiLpOwnerPart targetOwner targetBlock
              (Left (finitePiLpOwnerPart middleOwner middleBlock
                (Right f)))) ≤
          ∑ middleBlock,
            finitePiLpSupNorm
              (finitePiLpOwnerPart targetOwner targetBlock
                (Left (finitePiLpOwnerPart middleOwner middleBlock
                  (Right f)))) :=
        finitePiLpSupNorm_sum_le _
      _ ≤ ∑ middleBlock,
          leftCoefficient targetBlock middleBlock *
            finitePiLpSupNorm
              (finitePiLpOwnerPart middleOwner middleBlock (Right f)) := by
        apply Finset.sum_le_sum
        intro middleBlock _hmiddle
        exact hLeft.2 middleBlock
          (finitePiLpOwnerPart middleOwner middleBlock (Right f))
          (finitePiLpOwnerPart_supported middleOwner middleBlock (Right f))
          targetBlock
      _ ≤ ∑ middleBlock,
          (leftCoefficient targetBlock middleBlock *
            rightCoefficient middleBlock sourceBlock) *
              finitePiLpSupNorm f := by
        apply Finset.sum_le_sum
        intro middleBlock _hmiddle
        calc
          leftCoefficient targetBlock middleBlock *
              finitePiLpSupNorm
                (finitePiLpOwnerPart middleOwner middleBlock (Right f)) ≤
            leftCoefficient targetBlock middleBlock *
              (rightCoefficient middleBlock sourceBlock *
                finitePiLpSupNorm f) :=
            mul_le_mul_of_nonneg_left
              (hRight.2 sourceBlock f hf middleBlock)
              (hLeft.1 targetBlock middleBlock)
          _ = (leftCoefficient targetBlock middleBlock *
              rightCoefficient middleBlock sourceBlock) *
                finitePiLpSupNorm f := by ring
      _ = finiteOwnerKernelConvolution leftCoefficient rightCoefficient
            targetBlock sourceBlock * finitePiLpSupNorm f := by
        unfold finiteOwnerKernelConvolution
        rw [Finset.sum_mul]

/-- Output-fixed weighted rows are submultiplicative at the same spatial
rate.  The triangle inequality is the only metric input. -/
theorem finiteOwnerWeightedRowBound_convolution
    {β : Type*} [Fintype β]
    (dist : β → β → ℕ)
    (htri : ∀ targetBlock middleBlock sourceBlock,
      dist targetBlock sourceBlock ≤
        dist targetBlock middleBlock + dist middleBlock sourceBlock)
    {leftCoefficient rightCoefficient : β → β → ℝ}
    {A B rate : ℝ}
    (hLeftCoeff : ∀ targetBlock sourceBlock,
      0 ≤ leftCoefficient targetBlock sourceBlock)
    (hRightCoeff : ∀ targetBlock sourceBlock,
      0 ≤ rightCoefficient targetBlock sourceBlock)
    (hLeft : FiniteOwnerWeightedRowBound leftCoefficient dist A rate)
    (hRight : FiniteOwnerWeightedRowBound rightCoefficient dist B rate) :
    FiniteOwnerWeightedRowBound
      (finiteOwnerKernelConvolution leftCoefficient rightCoefficient)
      dist (A * B) rate := by
  refine ⟨mul_nonneg hLeft.1 hRight.1, hLeft.2.1, ?_⟩
  intro targetBlock
  have hweight : ∀ middleBlock sourceBlock,
      Real.exp (rate * (dist targetBlock sourceBlock : ℝ)) ≤
        Real.exp (rate * (dist targetBlock middleBlock : ℝ)) *
          Real.exp (rate * (dist middleBlock sourceBlock : ℝ)) := by
    intro middleBlock sourceBlock
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have htriReal : (dist targetBlock sourceBlock : ℝ) ≤
        (dist targetBlock middleBlock : ℝ) +
          (dist middleBlock sourceBlock : ℝ) := by
      exact_mod_cast htri targetBlock middleBlock sourceBlock
    calc
      rate * (dist targetBlock sourceBlock : ℝ) ≤
          rate * ((dist targetBlock middleBlock : ℝ) +
            (dist middleBlock sourceBlock : ℝ)) :=
        mul_le_mul_of_nonneg_left htriReal hLeft.2.1
      _ = rate * (dist targetBlock middleBlock : ℝ) +
          rate * (dist middleBlock sourceBlock : ℝ) := by ring
  calc
    ∑ sourceBlock : β,
          Real.exp (rate * (dist targetBlock sourceBlock : ℝ)) *
            finiteOwnerKernelConvolution leftCoefficient rightCoefficient
              targetBlock sourceBlock =
        ∑ sourceBlock : β, ∑ middleBlock : β,
          Real.exp (rate * (dist targetBlock sourceBlock : ℝ)) *
            (leftCoefficient targetBlock middleBlock *
              rightCoefficient middleBlock sourceBlock) := by
      apply Finset.sum_congr rfl
      intro sourceBlock _hsource
      unfold finiteOwnerKernelConvolution
      rw [Finset.mul_sum]
    _ = ∑ middleBlock : β, ∑ sourceBlock : β,
          Real.exp (rate * (dist targetBlock sourceBlock : ℝ)) *
            (leftCoefficient targetBlock middleBlock *
              rightCoefficient middleBlock sourceBlock) := by
      rw [Finset.sum_comm]
    _ ≤ ∑ middleBlock : β, ∑ sourceBlock : β,
          (Real.exp (rate * (dist targetBlock middleBlock : ℝ)) *
            leftCoefficient targetBlock middleBlock) *
          (Real.exp (rate * (dist middleBlock sourceBlock : ℝ)) *
            rightCoefficient middleBlock sourceBlock) := by
      apply Finset.sum_le_sum
      intro middleBlock _hmiddle
      apply Finset.sum_le_sum
      intro sourceBlock _hsource
      calc
        Real.exp (rate * (dist targetBlock sourceBlock : ℝ)) *
            (leftCoefficient targetBlock middleBlock *
              rightCoefficient middleBlock sourceBlock) ≤
          (Real.exp (rate * (dist targetBlock middleBlock : ℝ)) *
            Real.exp (rate * (dist middleBlock sourceBlock : ℝ))) *
              (leftCoefficient targetBlock middleBlock *
                rightCoefficient middleBlock sourceBlock) :=
          mul_le_mul_of_nonneg_right (hweight middleBlock sourceBlock)
            (mul_nonneg (hLeftCoeff targetBlock middleBlock)
              (hRightCoeff middleBlock sourceBlock))
        _ = (Real.exp (rate * (dist targetBlock middleBlock : ℝ)) *
              leftCoefficient targetBlock middleBlock) *
            (Real.exp (rate * (dist middleBlock sourceBlock : ℝ)) *
              rightCoefficient middleBlock sourceBlock) := by ring
    _ = ∑ middleBlock : β,
          (Real.exp (rate * (dist targetBlock middleBlock : ℝ)) *
            leftCoefficient targetBlock middleBlock) *
          (∑ sourceBlock : β,
            Real.exp (rate * (dist middleBlock sourceBlock : ℝ)) *
              rightCoefficient middleBlock sourceBlock) := by
      apply Finset.sum_congr rfl
      intro middleBlock _hmiddle
      rw [Finset.mul_sum]
    _ ≤ ∑ middleBlock : β,
          (Real.exp (rate * (dist targetBlock middleBlock : ℝ)) *
            leftCoefficient targetBlock middleBlock) * B := by
      apply Finset.sum_le_sum
      intro middleBlock _hmiddle
      exact mul_le_mul_of_nonneg_left (hRight.2.2 middleBlock)
        (mul_nonneg (Real.exp_pos _).le
          (hLeftCoeff targetBlock middleBlock))
    _ = (∑ middleBlock : β,
          Real.exp (rate * (dist targetBlock middleBlock : ℝ)) *
            leftCoefficient targetBlock middleBlock) * B := by
      rw [Finset.sum_mul]
    _ ≤ A * B := mul_le_mul_of_nonneg_right
      (hLeft.2.2 targetBlock) hRight.1

/-- Complete owner-weighted supremum certificates compose without losing
spatial rate and without introducing a carrier cardinality. -/
theorem finitePiLpTypedOwnerWeightedSupKernelBound_comp
    {ι κ ν β g : Type*}
    [Fintype ι] [Nonempty ι]
    [Fintype κ] [Nonempty κ]
    [Fintype ν] [Nonempty ν]
    [Fintype β] [DecidableEq β]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (dist : β → β → ℕ)
    (htri : ∀ targetBlock middleBlock sourceBlock,
      dist targetBlock sourceBlock ≤
        dist targetBlock middleBlock + dist middleBlock sourceBlock)
    {Left : FinitePiLpField κ g →L[ℝ] FinitePiLpField ν g}
    {Right : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g}
    {sourceOwner : ι → β} {middleOwner : κ → β} {targetOwner : ν → β}
    {leftCoefficient rightCoefficient : β → β → ℝ}
    {A B rate : ℝ}
    (hLeft : FinitePiLpTypedOwnerWeightedSupKernelBound
      Left middleOwner targetOwner leftCoefficient dist A rate)
    (hRight : FinitePiLpTypedOwnerWeightedSupKernelBound
      Right sourceOwner middleOwner rightCoefficient dist B rate) :
    FinitePiLpTypedOwnerWeightedSupKernelBound
      (Left.comp Right) sourceOwner targetOwner
      (finiteOwnerKernelConvolution leftCoefficient rightCoefficient)
      dist (A * B) rate := by
  exact ⟨finitePiLpTypedOwnerSupKernelBound_comp hLeft.1 hRight.1,
    finiteOwnerWeightedRowBound_convolution dist htri
      hLeft.1.1 hRight.1.1 hLeft.2 hRight.2⟩

end

end YangMills.RG
