/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.FinitePiLpCombesThomas

/-!
# Rectangular kernel predicates on finite dependent-index fields

Consecutive CMP99 regions have different site subtypes.  These predicates
record entry bounds, finite range and exponential decay without transporting
either operator through an equality of carriers.
-/

namespace YangMills.RG

noncomputable section

/-- Entrywise bound for a rectangular finite `PiLp` operator. -/
def FinitePiLpTypedKernelBound
    {ι κ g : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (C : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    (weight : κ → ι → ℝ) : Prop :=
  ∀ source target (v : g),
    ‖C (singleFinitePiLp source v) target‖ ≤
      weight target source * ‖v‖

/-- Exact finite range for a rectangular finite `PiLp` operator. -/
def FinitePiLpTypedFiniteRange
    {ι κ g : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (C : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    (dist : κ → ι → ℕ) (R : ℕ) : Prop :=
  ∀ source target (v : g), R < dist target source →
    C (singleFinitePiLp source v) target = 0

/-- Fixed-rate exponential bound for a rectangular finite `PiLp` operator. -/
def FinitePiLpTypedExponentialKernelBound
    {ι κ g : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (C : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    (dist : κ → ι → ℕ) (A rate : ℝ) : Prop :=
  0 ≤ A ∧ 0 < rate ∧
    ∀ source target (v : g),
      ‖C (singleFinitePiLp source v) target‖ ≤
        A * Real.exp (-(rate * (dist target source : ℝ))) * ‖v‖

/-- The operator norm supplies a rectangular entry budget. -/
theorem finitePiLpTypedKernelBound_const_opNorm
    {ι κ g : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (C : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g) :
    FinitePiLpTypedKernelBound C (fun _ _ => ‖C‖) := by
  intro source target v
  calc
    ‖C (singleFinitePiLp source v) target‖ ≤
        ‖C (singleFinitePiLp source v)‖ := PiLp.norm_apply_le _ target
    _ ≤ ‖C‖ * ‖singleFinitePiLp source v‖ :=
      ContinuousLinearMap.le_opNorm C _
    _ = ‖C‖ * ‖v‖ := by rw [norm_singleFinitePiLp]

/-- A square exponential bound is a rectangular bound with identical index
types. -/
theorem finitePiLpTypedExponentialKernelBound_of_square
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    {C : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g}
    {dist : ι → ι → ℕ} {A rate : ℝ}
    (hC : FinitePiLpExponentialKernelBound C dist A rate) :
    FinitePiLpTypedExponentialKernelBound C dist A rate := hC

/-- Exponential localization is stable under decreasing the positive rate. -/
theorem finitePiLpTypedExponentialKernelBound_mono_rate
    {ι κ g : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    {C : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g}
    {dist : κ → ι → ℕ} {A rate rate' : ℝ}
    (hrate' : 0 < rate') (hle : rate' ≤ rate)
    (hC : FinitePiLpTypedExponentialKernelBound C dist A rate) :
    FinitePiLpTypedExponentialKernelBound C dist A rate' := by
  refine ⟨hC.1, hrate', ?_⟩
  intro source target v
  refine (hC.2.2 source target v).trans ?_
  have hdist : (0 : ℝ) ≤ dist target source := by positivity
  have hexp : Real.exp (-(rate * (dist target source : ℝ))) ≤
      Real.exp (-(rate' * (dist target source : ℝ))) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hexp hC.1) (norm_nonneg v)

/-- Negation preserves a rectangular exponential kernel bound. -/
theorem finitePiLpTypedExponentialKernelBound_neg
    {ι κ g : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    {C : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g}
    {dist : κ → ι → ℕ} {A rate : ℝ}
    (hC : FinitePiLpTypedExponentialKernelBound C dist A rate) :
    FinitePiLpTypedExponentialKernelBound (-C) dist A rate := by
  refine ⟨hC.1, hC.2.1, ?_⟩
  intro source target v
  simpa only [ContinuousLinearMap.neg_apply, PiLp.neg_apply, norm_neg] using
    hC.2.2 source target v

/-- Addition preserves the rate and adds rectangular amplitudes. -/
theorem finitePiLpTypedExponentialKernelBound_add
    {ι κ g : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    {C D : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g}
    {dist : κ → ι → ℕ} {A B rate : ℝ}
    (hC : FinitePiLpTypedExponentialKernelBound C dist A rate)
    (hD : FinitePiLpTypedExponentialKernelBound D dist B rate) :
    FinitePiLpTypedExponentialKernelBound (C + D) dist (A + B) rate := by
  refine ⟨add_nonneg hC.1 hD.1, hC.2.1, ?_⟩
  intro source target v
  calc
    ‖(C + D) (singleFinitePiLp source v) target‖ ≤
        ‖C (singleFinitePiLp source v) target‖ +
          ‖D (singleFinitePiLp source v) target‖ := by
      rw [ContinuousLinearMap.add_apply, PiLp.add_apply]
      exact norm_add_le _ _
    _ ≤ A * Real.exp (-(rate * (dist target source : ℝ))) * ‖v‖ +
        B * Real.exp (-(rate * (dist target source : ℝ))) * ‖v‖ :=
      add_le_add (hC.2.2 source target v) (hD.2.2 source target v)
    _ = (A + B) * Real.exp (-(rate * (dist target source : ℝ))) * ‖v‖ := by
      ring

/-- A rectangular finite-range kernel is exponentially localized at every
positive rate, with the exact support cost `exp (rate * R)`. -/
theorem finitePiLpTypedExponentialKernelBound_of_finiteRange
    {ι κ g : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    {dist : κ → ι → ℕ} {beta rate : ℝ} {R : ℕ}
    (hbeta : 0 ≤ beta) (hrate : 0 < rate)
    (C : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    (hrange : FinitePiLpTypedFiniteRange C dist R)
    (hbound : FinitePiLpTypedKernelBound C (fun _ _ => beta)) :
    FinitePiLpTypedExponentialKernelBound
      C dist (beta * Real.exp (rate * (R : ℝ))) rate := by
  refine ⟨mul_nonneg hbeta (Real.exp_pos _).le, hrate, ?_⟩
  intro source target v
  by_cases hfar : R < dist target source
  · rw [hrange source target v hfar, norm_zero]
    positivity
  · have hnear : (dist target source : ℝ) ≤ (R : ℝ) := by
      exact_mod_cast le_of_not_gt hfar
    have hexp :
        1 ≤ Real.exp (rate * (R : ℝ)) *
          Real.exp (-(rate * (dist target source : ℝ))) := by
      rw [← Real.exp_add, ← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      nlinarith
    calc
      ‖C (singleFinitePiLp source v) target‖ ≤ beta * ‖v‖ :=
        hbound source target v
      _ ≤ beta *
          (Real.exp (rate * (R : ℝ)) *
            Real.exp (-(rate * (dist target source : ℝ)))) * ‖v‖ := by
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hexp hbeta) (norm_nonneg v)
        simpa using this
      _ = (beta * Real.exp (rate * (R : ℝ))) *
          Real.exp (-(rate * (dist target source : ℝ))) * ‖v‖ := by ring

/-- Composition of rectangular exponential kernels at a fixed input rate.
One positive rate margin is spent on a volume-uniform exponential row sum
over the intermediate carrier. -/
theorem finitePiLpTypedExponentialKernelBound_comp
    {ι κ ν g : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype ν]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (distLK : ν → κ → ℕ) (distKI : κ → ι → ℕ)
    (distLI : ν → ι → ℕ)
    (htri : ∀ target middle source,
      distLI target source ≤ distLK target middle + distKI middle source)
    {A B rate sigma S : ℝ}
    (hsigma : 0 < sigma) (hsigmaRate : sigma < rate) (hS : 0 ≤ S)
    (hsum : ∀ target : ν,
      ∑ middle : κ,
        Real.exp (-(sigma * (distLK target middle : ℝ))) ≤ S)
    (Left : FinitePiLpField κ g →L[ℝ] FinitePiLpField ν g)
    (Right : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    (hLeft : FinitePiLpTypedExponentialKernelBound Left distLK A rate)
    (hRight : FinitePiLpTypedExponentialKernelBound Right distKI B rate) :
    FinitePiLpTypedExponentialKernelBound
      (Left.comp Right) distLI (A * B * S) (rate - sigma) := by
  classical
  refine ⟨mul_nonneg (mul_nonneg hLeft.1 hRight.1) hS,
    sub_pos.mpr hsigmaRate, ?_⟩
  intro source target v
  let probe := singleFinitePiLp source v
  have hdecomp : Right probe =
      ∑ middle, singleFinitePiLp middle (Right probe middle) :=
    (sum_singleFinitePiLp_eq (Right probe)).symm
  have happ : Left (Right probe) target =
      ∑ middle, Left (singleFinitePiLp middle (Right probe middle)) target := by
    calc
      Left (Right probe) target =
          Left (∑ middle, singleFinitePiLp middle (Right probe middle)) target :=
        congrArg (fun f => Left f target) hdecomp
      _ = (∑ middle,
          Left (singleFinitePiLp middle (Right probe middle))) target := by
        rw [map_sum]
      _ = ∑ middle,
          Left (singleFinitePiLp middle (Right probe middle)) target :=
        finitePiLp_sum_apply _ _ _
  rw [ContinuousLinearMap.comp_apply, happ]
  calc
    ‖∑ middle, Left (singleFinitePiLp middle (Right probe middle)) target‖ ≤
        ∑ middle,
          ‖Left (singleFinitePiLp middle (Right probe middle)) target‖ :=
      norm_sum_le _ _
    _ ≤ ∑ middle,
        (A * Real.exp (-(rate * (distLK target middle : ℝ))) *
          (B * Real.exp (-(rate * (distKI middle source : ℝ))) * ‖v‖)) := by
      apply Finset.sum_le_sum
      intro middle _
      exact (hLeft.2.2 middle target (Right probe middle)).trans
        (mul_le_mul_of_nonneg_left
          (hRight.2.2 source middle v)
          (mul_nonneg hLeft.1 (Real.exp_pos _).le))
    _ ≤ ∑ middle,
        ((A * B) *
          Real.exp (-((rate - sigma) * (distLI target source : ℝ))) *
          Real.exp (-(sigma * (distLK target middle : ℝ))) * ‖v‖) := by
      apply Finset.sum_le_sum
      intro middle _
      have hdist : (distLI target source : ℝ) ≤
          (distLK target middle : ℝ) + (distKI middle source : ℝ) := by
        exact_mod_cast htri target middle source
      have hexp :
          Real.exp (-(rate * (distLK target middle : ℝ))) *
              Real.exp (-(rate * (distKI middle source : ℝ))) ≤
            Real.exp (-((rate - sigma) * (distLI target source : ℝ))) *
              Real.exp (-(sigma * (distLK target middle : ℝ))) := by
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hLK : (0 : ℝ) ≤ distLK target middle := by positivity
        have hKI : (0 : ℝ) ≤ distKI middle source := by positivity
        nlinarith
      have hAB : 0 ≤ A * B := mul_nonneg hLeft.1 hRight.1
      have hv : 0 ≤ ‖v‖ := norm_nonneg v
      calc
        A * Real.exp (-(rate * (distLK target middle : ℝ))) *
            (B * Real.exp (-(rate * (distKI middle source : ℝ))) * ‖v‖) =
          (A * B) *
            (Real.exp (-(rate * (distLK target middle : ℝ))) *
              Real.exp (-(rate * (distKI middle source : ℝ)))) * ‖v‖ := by ring
        _ ≤ (A * B) *
            (Real.exp (-((rate - sigma) * (distLI target source : ℝ))) *
              Real.exp (-(sigma * (distLK target middle : ℝ)))) * ‖v‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hexp hAB) hv
        _ = (A * B) *
            Real.exp (-((rate - sigma) * (distLI target source : ℝ))) *
            Real.exp (-(sigma * (distLK target middle : ℝ))) * ‖v‖ := by ring
    _ = ((A * B) *
          Real.exp (-((rate - sigma) * (distLI target source : ℝ))) * ‖v‖) *
        ∑ middle, Real.exp (-(sigma * (distLK target middle : ℝ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro middle _
      ring
    _ ≤ ((A * B) *
          Real.exp (-((rate - sigma) * (distLI target source : ℝ))) * ‖v‖) * S := by
      apply mul_le_mul_of_nonneg_left (hsum target)
      exact mul_nonneg
        (mul_nonneg (mul_nonneg hLeft.1 hRight.1) (Real.exp_pos _).le)
        (norm_nonneg v)
    _ = (A * B * S) *
        Real.exp (-((rate - sigma) * (distLI target source : ℝ))) * ‖v‖ := by
      ring

end

end YangMills.RG
