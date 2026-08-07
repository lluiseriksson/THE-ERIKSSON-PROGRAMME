/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.FinitePiLpOwnerWeightedSupKernelPowerSummability

/-!
# Owner-weighted Neumann series at fixed spatial rate

For a strict owner-sup contraction `A < 1`, the already constructed operator
powers and their literal convolution coefficients are summable.  This module
forms both `tsum`s and proves that the resulting operator has the output-fixed
weighted owner row `(1 - A)⁻¹` at the unchanged spatial rate.

This is the convergent Neumann object and its quantitative kernel bound.  The
left/right inverse identities, the physical CMP99 specialization, uniform
production of `B0` and `delta0`, and attainment of window 15 remain separate.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

/-- Literal owner-block coefficient of the convergent Neumann series. -/
noncomputable def finiteOwnerKernelNeumannCoefficient
    {β : Type*} [Fintype β] [DecidableEq β]
    (coefficient : β → β → ℝ) (targetBlock sourceBlock : β) : ℝ :=
  ∑' n : ℕ, finiteOwnerKernelPower coefficient n targetBlock sourceBlock

/-- One coefficient of every owner-kernel power is dominated by the same
geometric amplitude that bounds its complete output row. -/
theorem finiteOwnerKernelPower_le_geometricAmplitude
    {ι β g : Type*}
    [Fintype ι] [Nonempty ι]
    [Fintype β] [DecidableEq β]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (dist : β → β → ℕ)
    (hdiag : ∀ owner, dist owner owner = 0)
    (htri : ∀ targetBlock middleBlock sourceBlock,
      dist targetBlock sourceBlock ≤
        dist targetBlock middleBlock + dist middleBlock sourceBlock)
    {T : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g}
    {ownerMap : ι → β} {coefficient : β → β → ℝ}
    {A rate : ℝ}
    (hT : FinitePiLpTypedOwnerWeightedSupKernelBound
      T ownerMap ownerMap coefficient dist A rate)
    (n : ℕ) (targetBlock sourceBlock : β) :
    finiteOwnerKernelPower coefficient n targetBlock sourceBlock ≤ A ^ n := by
  have hpow := finitePiLpTypedOwnerWeightedSupKernelBound_pow
    dist hdiag htri hT n
  have hnonneg := hpow.1.1 targetBlock sourceBlock
  calc
    finiteOwnerKernelPower coefficient n targetBlock sourceBlock =
        1 * finiteOwnerKernelPower coefficient n targetBlock sourceBlock := by
      ring
    _ ≤ Real.exp (rate * (dist targetBlock sourceBlock : ℝ)) *
          finiteOwnerKernelPower coefficient n targetBlock sourceBlock :=
      mul_le_mul_of_nonneg_right
        (Real.one_le_exp
          (mul_nonneg hT.2.2.1 (Nat.cast_nonneg _))) hnonneg
    _ ≤ ∑ middleBlock : β,
          Real.exp (rate * (dist targetBlock middleBlock : ℝ)) *
            finiteOwnerKernelPower coefficient n targetBlock middleBlock :=
      Finset.single_le_sum
        (s := Finset.univ)
        (f := fun middleBlock : β =>
          Real.exp (rate * (dist targetBlock middleBlock : ℝ)) *
            finiteOwnerKernelPower coefficient n targetBlock middleBlock)
        (fun middleBlock _ => mul_nonneg (Real.exp_pos _).le
          (hpow.1.1 targetBlock middleBlock))
        (Finset.mem_univ sourceBlock)
    _ ≤ A ^ n := hpow.2.2.2 targetBlock

/-- Every literal owner-block coefficient power is summable under the one
strict owner-sup contraction. -/
theorem summable_finiteOwnerKernelPower
    {ι β g : Type*}
    [Fintype ι] [Nonempty ι]
    [Fintype β] [DecidableEq β]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (dist : β → β → ℕ)
    (hdiag : ∀ owner, dist owner owner = 0)
    (htri : ∀ targetBlock middleBlock sourceBlock,
      dist targetBlock sourceBlock ≤
        dist targetBlock middleBlock + dist middleBlock sourceBlock)
    {T : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g}
    {ownerMap : ι → β} {coefficient : β → β → ℝ}
    {A rate : ℝ}
    (hT : FinitePiLpTypedOwnerWeightedSupKernelBound
      T ownerMap ownerMap coefficient dist A rate)
    (hsmall : A < 1) (targetBlock sourceBlock : β) :
    Summable fun n : ℕ =>
      finiteOwnerKernelPower coefficient n targetBlock sourceBlock := by
  apply Summable.of_nonneg_of_le
    (fun n =>
      (finitePiLpTypedOwnerWeightedSupKernelBound_pow
        dist hdiag htri hT n).1.1 targetBlock sourceBlock)
    (fun n => finiteOwnerKernelPower_le_geometricAmplitude
      dist hdiag htri hT n targetBlock sourceBlock)
    (summable_geometric_of_lt_one hT.2.1 hsmall)

/-- The literal Neumann coefficient is nonnegative entrywise. -/
theorem finiteOwnerKernelNeumannCoefficient_nonneg
    {ι β g : Type*}
    [Fintype ι] [Nonempty ι]
    [Fintype β] [DecidableEq β]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (dist : β → β → ℕ)
    (hdiag : ∀ owner, dist owner owner = 0)
    (htri : ∀ targetBlock middleBlock sourceBlock,
      dist targetBlock sourceBlock ≤
        dist targetBlock middleBlock + dist middleBlock sourceBlock)
    {T : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g}
    {ownerMap : ι → β} {coefficient : β → β → ℝ}
    {A rate : ℝ}
    (hT : FinitePiLpTypedOwnerWeightedSupKernelBound
      T ownerMap ownerMap coefficient dist A rate)
    (targetBlock sourceBlock : β) :
    0 ≤ finiteOwnerKernelNeumannCoefficient coefficient
      targetBlock sourceBlock := by
  unfold finiteOwnerKernelNeumannCoefficient
  exact tsum_nonneg fun n =>
    (finitePiLpTypedOwnerWeightedSupKernelBound_pow
      dist hdiag htri hT n).1.1 targetBlock sourceBlock

/-- The coefficient `tsum` has the exact geometric output-row amplitude and
retains the original spatial rate. -/
theorem finiteOwnerWeightedRowBound_neumann
    {ι β g : Type*}
    [Fintype ι] [Nonempty ι]
    [Fintype β] [DecidableEq β]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (dist : β → β → ℕ)
    (hdiag : ∀ owner, dist owner owner = 0)
    (htri : ∀ targetBlock middleBlock sourceBlock,
      dist targetBlock sourceBlock ≤
        dist targetBlock middleBlock + dist middleBlock sourceBlock)
    {T : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g}
    {ownerMap : ι → β} {coefficient : β → β → ℝ}
    {A rate : ℝ}
    (hT : FinitePiLpTypedOwnerWeightedSupKernelBound
      T ownerMap ownerMap coefficient dist A rate)
    (hsmall : A < 1) :
    FiniteOwnerWeightedRowBound
      (finiteOwnerKernelNeumannCoefficient coefficient)
      dist (1 - A)⁻¹ rate := by
  refine ⟨inv_nonneg.mpr (sub_nonneg.mpr hsmall.le), hT.2.2.1, ?_⟩
  intro targetBlock
  have hgeo : Summable fun n : ℕ => A ^ n :=
    summable_geometric_of_lt_one hT.2.1 hsmall
  have hcoefficientSummable (sourceBlock : β) :
      Summable fun n : ℕ =>
        finiteOwnerKernelPower coefficient n targetBlock sourceBlock :=
    summable_finiteOwnerKernelPower
      dist hdiag htri hT hsmall targetBlock sourceBlock
  have hweightedSummable (sourceBlock : β) :
      Summable fun n : ℕ =>
        Real.exp (rate * (dist targetBlock sourceBlock : ℝ)) *
          finiteOwnerKernelPower coefficient n targetBlock sourceBlock :=
    (hcoefficientSummable sourceBlock).mul_left
      (Real.exp (rate * (dist targetBlock sourceBlock : ℝ)))
  have hweightedFinsetSummable (sources : Finset β) :
      Summable fun n : ℕ =>
        ∑ sourceBlock ∈ sources,
          Real.exp (rate * (dist targetBlock sourceBlock : ℝ)) *
            finiteOwnerKernelPower coefficient n targetBlock sourceBlock := by
    classical
    induction sources using Finset.induction_on with
    | empty => simp
    | @insert sourceBlock sources hnot ih =>
        simpa only [Finset.sum_insert hnot] using
          (hweightedSummable sourceBlock).add ih
  have hrowSummable : Summable fun n : ℕ =>
      ∑ sourceBlock : β,
        Real.exp (rate * (dist targetBlock sourceBlock : ℝ)) *
          finiteOwnerKernelPower coefficient n targetBlock sourceBlock := by
    apply Summable.of_nonneg_of_le
      (fun n => Finset.sum_nonneg fun sourceBlock _ =>
        mul_nonneg (Real.exp_pos _).le
          ((finitePiLpTypedOwnerWeightedSupKernelBound_pow
            dist hdiag htri hT n).1.1 targetBlock sourceBlock))
      (fun n =>
        (finitePiLpTypedOwnerWeightedSupKernelBound_pow
          dist hdiag htri hT n).2.2.2 targetBlock)
      hgeo
  calc
    ∑ sourceBlock : β,
          Real.exp (rate * (dist targetBlock sourceBlock : ℝ)) *
            finiteOwnerKernelNeumannCoefficient coefficient
              targetBlock sourceBlock =
        ∑ sourceBlock : β, ∑' n : ℕ,
          Real.exp (rate * (dist targetBlock sourceBlock : ℝ)) *
            finiteOwnerKernelPower coefficient n targetBlock sourceBlock := by
      apply Finset.sum_congr rfl
      intro sourceBlock _hsource
      unfold finiteOwnerKernelNeumannCoefficient
      rw [tsum_mul_left]
    _ = ∑' n : ℕ, ∑ sourceBlock : β,
          Real.exp (rate * (dist targetBlock sourceBlock : ℝ)) *
            finiteOwnerKernelPower coefficient n targetBlock sourceBlock := by
      classical
      induction (Finset.univ : Finset β) using Finset.induction_on with
      | empty => simp
      | @insert sourceBlock sources hnot ih =>
          rw [Finset.sum_insert hnot, ih,
            ← (hweightedSummable sourceBlock).tsum_add
              (hweightedFinsetSummable sources)]
          apply tsum_congr
          intro n
          rw [Finset.sum_insert hnot]
    _ ≤ ∑' n : ℕ, A ^ n :=
      hrowSummable.tsum_le_tsum
        (fun n =>
          (finitePiLpTypedOwnerWeightedSupKernelBound_pow
            dist hdiag htri hT n).2.2.2 targetBlock)
        hgeo
    _ = (1 - A)⁻¹ := tsum_geometric_of_lt_one hT.2.1 hsmall

/-- The operator `tsum` acts between complete owner fibres with the literal
coefficient `tsum`. -/
theorem finitePiLpTypedOwnerSupKernelBound_neumann
    {ι β g : Type*}
    [Fintype ι] [Nonempty ι]
    [Fintype β] [DecidableEq β]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (dist : β → β → ℕ)
    (hdiag : ∀ owner, dist owner owner = 0)
    (htri : ∀ targetBlock middleBlock sourceBlock,
      dist targetBlock sourceBlock ≤
        dist targetBlock middleBlock + dist middleBlock sourceBlock)
    {T : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g}
    {ownerMap : ι → β} {coefficient : β → β → ℝ}
    {A rate : ℝ}
    (hT : FinitePiLpTypedOwnerWeightedSupKernelBound
      T ownerMap ownerMap coefficient dist A rate)
    (hsmall : A < 1) :
    FinitePiLpTypedOwnerSupKernelBound
      (∑' n : ℕ, T ^ n) ownerMap ownerMap
      (finiteOwnerKernelNeumannCoefficient coefficient) := by
  have hoperator := summable_finitePiLp_ownerWeighted_pow
    dist hdiag htri hT hsmall
  refine ⟨?_, ?_⟩
  · intro targetBlock sourceBlock
    exact finiteOwnerKernelNeumannCoefficient_nonneg
      dist hdiag htri hT targetBlock sourceBlock
  · intro sourceBlock f hf targetBlock
    let E := FinitePiLpField ι g
    let siteEval (target : ι) : E →L[ℝ] g :=
      (ContinuousLinearMap.proj target).comp
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => g)).toContinuousLinearMap
    let evalCLM (target : ι) :
        (E →L[ℝ] E) →L[ℝ] g :=
      (siteEval target).comp (ContinuousLinearMap.apply ℝ E f)
    have heval (target : ι) (S : E →L[ℝ] E) :
        evalCLM target S = S f target := by
      rfl
    have hrewrite (target : ι) :
        (∑' n : ℕ, T ^ n) f target = ∑' n : ℕ, (T ^ n) f target := by
      simpa only [heval] using (evalCLM target).map_tsum hoperator
    have hcoefficientSummable := summable_finiteOwnerKernelPower
      dist hdiag htri hT hsmall targetBlock sourceBlock
    have hmajor : Summable fun n : ℕ =>
        finiteOwnerKernelPower coefficient n targetBlock sourceBlock *
          finitePiLpSupNorm f :=
      hcoefficientSummable.mul_right (finitePiLpSupNorm f)
    apply finitePiLpSupNorm_le_of_norm_apply_le
    intro target
    rw [finitePiLpOwnerPart_apply]
    by_cases htarget : ownerMap target = targetBlock
    · rw [if_pos htarget, hrewrite target]
      have hterm_le (n : ℕ) :
          ‖(T ^ n) f target‖ ≤
            finiteOwnerKernelPower coefficient n targetBlock sourceBlock *
              finitePiLpSupNorm f := by
        calc
          ‖(T ^ n) f target‖ =
              ‖finitePiLpOwnerPart ownerMap targetBlock ((T ^ n) f) target‖ := by
            rw [finitePiLpOwnerPart_apply, if_pos htarget]
          _ ≤ finitePiLpSupNorm
                (finitePiLpOwnerPart ownerMap targetBlock ((T ^ n) f)) :=
            norm_apply_le_finitePiLpSupNorm _ target
          _ ≤ finiteOwnerKernelPower coefficient n targetBlock sourceBlock *
                finitePiLpSupNorm f :=
            (finitePiLpTypedOwnerWeightedSupKernelBound_pow
              dist hdiag htri hT n).1.2 sourceBlock f hf targetBlock
      have hnormSummable : Summable fun n : ℕ => ‖(T ^ n) f target‖ :=
        Summable.of_nonneg_of_le
          (fun n => norm_nonneg _) hterm_le hmajor
      calc
        ‖∑' n : ℕ, (T ^ n) f target‖ ≤
            ∑' n : ℕ, ‖(T ^ n) f target‖ :=
          norm_tsum_le_tsum_norm hnormSummable
        _ ≤ ∑' n : ℕ,
              finiteOwnerKernelPower coefficient n targetBlock sourceBlock *
                finitePiLpSupNorm f :=
          hnormSummable.tsum_le_tsum hterm_le hmajor
        _ = finiteOwnerKernelNeumannCoefficient coefficient
              targetBlock sourceBlock * finitePiLpSupNorm f := by
          unfold finiteOwnerKernelNeumannCoefficient
          rw [tsum_mul_right]
    · rw [if_neg htarget, norm_zero]
      exact mul_nonneg
        (finiteOwnerKernelNeumannCoefficient_nonneg
          dist hdiag htri hT targetBlock sourceBlock)
        (finitePiLpSupNorm_nonneg f)

/-- Complete fixed-rate owner-weighted certificate for the literal Neumann
operator `tsum`. -/
theorem finitePiLpTypedOwnerWeightedSupKernelBound_neumann
    {ι β g : Type*}
    [Fintype ι] [Nonempty ι]
    [Fintype β] [DecidableEq β]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (dist : β → β → ℕ)
    (hdiag : ∀ owner, dist owner owner = 0)
    (htri : ∀ targetBlock middleBlock sourceBlock,
      dist targetBlock sourceBlock ≤
        dist targetBlock middleBlock + dist middleBlock sourceBlock)
    {T : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g}
    {ownerMap : ι → β} {coefficient : β → β → ℝ}
    {A rate : ℝ}
    (hT : FinitePiLpTypedOwnerWeightedSupKernelBound
      T ownerMap ownerMap coefficient dist A rate)
    (hsmall : A < 1) :
    FinitePiLpTypedOwnerWeightedSupKernelBound
      (∑' n : ℕ, T ^ n) ownerMap ownerMap
      (finiteOwnerKernelNeumannCoefficient coefficient)
      dist (1 - A)⁻¹ rate := by
  exact ⟨finitePiLpTypedOwnerSupKernelBound_neumann
      dist hdiag htri hT hsmall,
    finiteOwnerWeightedRowBound_neumann dist hdiag htri hT hsmall⟩

end

end YangMills.RG
