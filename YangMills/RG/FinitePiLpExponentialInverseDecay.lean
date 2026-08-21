/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.FinitePiLpCombesThomas

/-!
# A canonical fixed-rate inverse bound for exponential finite kernels

This file packages the scalar tilt budget used when an exponentially
localized coercive operator is inverted.  The inverse rate is chosen from the
available decay, coercivity, amplitude, and a volume-independent exponential
row sum.  No physical hypothesis is introduced here.

PRE-VALIDATION (C6c.4b): the canonical-rate positivity and rooted tilted
coercivity factorization are present in source but their revised `.olean` and
audit have not yet been materialized by the Lean compiler.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

private theorem exp_sub_one_le_mul_exp_of_nonneg {x : ℝ} (_hx : 0 ≤ x) :
    Real.exp x - 1 ≤ x * Real.exp x := by
  have hbase := Real.add_one_le_exp (-x)
  have hsmall : 1 - Real.exp (-x) ≤ x := by linarith
  have hmul := mul_le_mul_of_nonneg_left hsmall (Real.exp_pos x).le
  have hinv : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  nlinarith

private theorem exponentialTiltWeight_le
    {rate decay : ℝ} (hrate : 0 ≤ rate) (hdecay : 0 < decay)
    (hrateHalf : rate ≤ decay / 2) (n : ℕ) :
    (Real.exp (rate * (n : ℝ)) - 1) *
        Real.exp (-(decay * (n : ℝ))) ≤
      rate * (4 / decay) *
        Real.exp (-((decay / 4) * (n : ℝ))) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hx : 0 ≤ rate * (n : ℝ) := mul_nonneg hrate hn
  have hfirst := exp_sub_one_le_mul_exp_of_nonneg hx
  have hfirst' :
      (Real.exp (rate * (n : ℝ)) - 1) *
          Real.exp (-(decay * (n : ℝ))) ≤
        (rate * (n : ℝ) * Real.exp (rate * (n : ℝ))) *
          Real.exp (-(decay * (n : ℝ))) :=
    mul_le_mul_of_nonneg_right hfirst (Real.exp_pos _).le
  have hexact :
      (rate * (n : ℝ) * Real.exp (rate * (n : ℝ))) *
          Real.exp (-(decay * (n : ℝ))) =
        rate * (n : ℝ) *
          Real.exp (-((decay - rate) * (n : ℝ))) := by
    calc
      (rate * (n : ℝ) * Real.exp (rate * (n : ℝ))) *
          Real.exp (-(decay * (n : ℝ))) =
        rate * (n : ℝ) *
          (Real.exp (rate * (n : ℝ)) *
            Real.exp (-(decay * (n : ℝ)))) := by ring
      _ = rate * (n : ℝ) *
          Real.exp (rate * (n : ℝ) - decay * (n : ℝ)) := by
        rw [← Real.exp_add]
        congr 2
      _ = rate * (n : ℝ) *
          Real.exp (-((decay - rate) * (n : ℝ))) := by ring_nf
  have hhalf : decay / 2 ≤ decay - rate := by linarith
  have hexpHalf :
      Real.exp (-((decay - rate) * (n : ℝ))) ≤
        Real.exp (-((decay / 2) * (n : ℝ))) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hsecond :
      rate * (n : ℝ) * Real.exp (-((decay - rate) * (n : ℝ))) ≤
        rate * (n : ℝ) * Real.exp (-((decay / 2) * (n : ℝ))) :=
    mul_le_mul_of_nonneg_left hexpHalf (mul_nonneg hrate hn)
  have hzexp : (decay / 4) * (n : ℝ) ≤
      Real.exp ((decay / 4) * (n : ℝ)) := by
    linarith [Real.add_one_le_exp ((decay / 4) * (n : ℝ))]
  have hnexp : (n : ℝ) ≤
      (4 / decay) * Real.exp ((decay / 4) * (n : ℝ)) := by
    have h := mul_le_mul_of_nonneg_left hzexp
      (show 0 ≤ 4 / decay by positivity)
    have hident : (4 / decay) * ((decay / 4) * (n : ℝ)) = (n : ℝ) := by
      field_simp
    simpa [hident] using h
  have hthird :
      rate * (n : ℝ) * Real.exp (-((decay / 2) * (n : ℝ))) ≤
        rate * ((4 / decay) * Real.exp ((decay / 4) * (n : ℝ))) *
          Real.exp (-((decay / 2) * (n : ℝ))) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hnexp hrate) (Real.exp_pos _).le
  calc
    (Real.exp (rate * (n : ℝ)) - 1) *
        Real.exp (-(decay * (n : ℝ))) ≤
      rate * (n : ℝ) * Real.exp (-((decay - rate) * (n : ℝ))) := by
        rw [← hexact]
        exact hfirst'
    _ ≤ rate * (n : ℝ) * Real.exp (-((decay / 2) * (n : ℝ))) := hsecond
    _ ≤ rate * ((4 / decay) * Real.exp ((decay / 4) * (n : ℝ))) *
        Real.exp (-((decay / 2) * (n : ℝ))) := hthird
    _ = rate * (4 / decay) *
        Real.exp (-((decay / 4) * (n : ℝ))) := by
      calc
        rate * ((4 / decay) * Real.exp ((decay / 4) * (n : ℝ))) *
            Real.exp (-((decay / 2) * (n : ℝ))) =
          rate * (4 / decay) *
            (Real.exp ((decay / 4) * (n : ℝ)) *
              Real.exp (-((decay / 2) * (n : ℝ)))) := by ring
        _ = rate * (4 / decay) *
            Real.exp ((decay / 4) * (n : ℝ) -
              (decay / 2) * (n : ℝ)) := by
          rw [← Real.exp_add]
          congr 2
        _ = rate * (4 / decay) *
            Real.exp (-((decay / 4) * (n : ℝ))) := by ring_nf

/-- Canonical rate left after spending half the coercivity in the exponential
tilt argument. -/
noncomputable def finitePiLpExponentialInverseDecayRate
    (amplitude decay rowSum coercivity : ℝ) : ℝ :=
  min (decay / 2)
    (coercivity * decay / (8 * (amplitude * rowSum + 1)))

/-- The canonical inverse rate is positive whenever the original decay and
coercivity are positive and the amplitude and row sum are nonnegative. -/
theorem finitePiLpExponentialInverseDecayRate_pos
    {amplitude decay rowSum coercivity : ℝ}
    (hamplitude : 0 ≤ amplitude) (hdecay : 0 < decay)
    (hrowSum : 0 ≤ rowSum) (hcoercivity : 0 < coercivity) :
    0 < finitePiLpExponentialInverseDecayRate
      amplitude decay rowSum coercivity := by
  unfold finitePiLpExponentialInverseDecayRate
  exact lt_min (by positivity) (by positivity)

set_option maxHeartbeats 1200000 in
/-- The canonical inverse-rate calculation already proves that every rooted
tilted precision retains half the original coercivity.  This is the
arbitrary-input intermediate fact hidden by point-source kernel extraction. -/
theorem isCoerciveCLM_finitePiLpTiltConj_inverse_canonical
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [InnerProductSpace ℝ g] [FiniteDimensional ℝ g]
    (dist : ι → ι → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    (htri : ∀ p q r, dist p r ≤ dist p q + dist q r)
    (K : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g)
    {amplitude decay rowSum coercivity : ℝ}
    (hdecay : 0 < decay) (hcoercivity : 0 < coercivity)
    (hrowSum : 0 ≤ rowSum)
    (hK : FinitePiLpExponentialKernelBound K dist amplitude decay)
    (hcoer : IsCoerciveCLM K coercivity)
    (hexpSum : ∀ target,
      ∑ source, Real.exp (-((decay / 4) * (dist target source : ℝ))) ≤
        rowSum)
    (root : ι) :
    IsCoerciveCLM
      (finitePiLpTiltConjCLM dist
        (finitePiLpExponentialInverseDecayRate
          amplitude decay rowSum coercivity) root K)
      (coercivity / 2) := by
  let rate := finitePiLpExponentialInverseDecayRate
    amplitude decay rowSum coercivity
  have hamplitude : 0 ≤ amplitude := hK.1
  have hrate : 0 < rate := by
    exact finitePiLpExponentialInverseDecayRate_pos
      hamplitude hdecay hrowSum hcoercivity
  have hrateHalf : rate ≤ decay / 2 := by
    dsimp [rate, finitePiLpExponentialInverseDecayRate]
    exact min_le_left _ _
  have hsum : ∀ target,
      ∑ source,
        (Real.exp (rate * (dist target source : ℝ)) - 1) *
          Real.exp (-(decay * (dist target source : ℝ))) ≤
        rate * (4 / decay) * rowSum := by
    intro target
    calc
      ∑ source,
          (Real.exp (rate * (dist target source : ℝ)) - 1) *
            Real.exp (-(decay * (dist target source : ℝ))) ≤
        ∑ source, rate * (4 / decay) *
          Real.exp (-((decay / 4) * (dist target source : ℝ))) :=
          Finset.sum_le_sum (fun source _ =>
            exponentialTiltWeight_le hrate.le hdecay hrateHalf _)
      _ = (rate * (4 / decay)) *
          ∑ source, Real.exp (-((decay / 4) *
            (dist target source : ℝ))) := by rw [Finset.mul_sum]
      _ ≤ (rate * (4 / decay)) * rowSum :=
        mul_le_mul_of_nonneg_left (hexpSum target) (by positivity)
      _ = rate * (4 / decay) * rowSum := by ring
  have hbudget :
      amplitude * (rate * (4 / decay) * rowSum) ≤ coercivity / 2 := by
    have hrateBudget : rate ≤
        coercivity * decay / (8 * (amplitude * rowSum + 1)) := by
      dsimp [rate, finitePiLpExponentialInverseDecayRate]
      exact min_le_right _ _
    have hden : 0 < amplitude * rowSum + 1 := by positivity
    have hmul := mul_le_mul_of_nonneg_right hrateBudget
      (show 0 ≤ (4 / decay) * (amplitude * rowSum) by positivity)
    have hquot :
        (amplitude * rowSum) / (amplitude * rowSum + 1) ≤ 1 := by
      apply (div_le_one hden).2
      linarith
    have hcalc :
        (coercivity * decay / (8 * (amplitude * rowSum + 1))) *
            ((4 / decay) * (amplitude * rowSum)) =
          coercivity / 2 *
            ((amplitude * rowSum) / (amplitude * rowSum + 1)) := by
      field_simp
      ring
    calc
      amplitude * (rate * (4 / decay) * rowSum) =
          rate * ((4 / decay) * (amplitude * rowSum)) := by ring
      _ ≤ (coercivity * decay / (8 * (amplitude * rowSum + 1))) *
          ((4 / decay) * (amplitude * rowSum)) := hmul
      _ = coercivity / 2 *
          ((amplitude * rowSum) / (amplitude * rowSum + 1)) := hcalc
      _ ≤ coercivity / 2 * 1 :=
        mul_le_mul_of_nonneg_left hquot (by positivity)
      _ = coercivity / 2 := by ring
  have htilt := isCoerciveCLM_finitePiLpTiltConj_of_exponential
    dist hsymm htri hrate.le root
    (mul_nonneg (mul_nonneg hrate.le (by positivity)) hrowSum)
    hsum hK hcoer
  intro x
  calc
    coercivity / 2 * ‖x‖ ^ 2 ≤
        (coercivity - amplitude * (rate * (4 / decay) * rowSum)) *
          ‖x‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg ‖x‖)
      linarith
    _ ≤ inner ℝ x (finitePiLpTiltConjCLM dist rate root K x) := htilt x

set_option maxHeartbeats 1200000 in
/-- An exponentially localized coercive finite kernel has an exponentially
localized inverse at the canonical rate.  The caller supplies only the
unweighted exponential row sum at one quarter of the original decay. -/
theorem finitePiLpExponentialKernelBound_inverse_canonical
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [InnerProductSpace ℝ g] [FiniteDimensional ℝ g]
    (dist : ι → ι → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    (htri : ∀ p q r, dist p r ≤ dist p q + dist q r)
    (hself : ∀ p, dist p p = 0)
    (K C : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g)
    {amplitude decay rowSum coercivity : ℝ}
    (hdecay : 0 < decay) (hcoercivity : 0 < coercivity)
    (hrowSum : 0 ≤ rowSum)
    (hK : FinitePiLpExponentialKernelBound K dist amplitude decay)
    (hcoer : IsCoerciveCLM K coercivity)
    (hKC : K.comp C = ContinuousLinearMap.id ℝ _)
    (hexpSum : ∀ target,
      ∑ source, Real.exp (-((decay / 4) * (dist target source : ℝ))) ≤
        rowSum) :
    FinitePiLpExponentialKernelBound C dist (2 / coercivity)
      (finitePiLpExponentialInverseDecayRate
        amplitude decay rowSum coercivity) := by
  let rate := finitePiLpExponentialInverseDecayRate
    amplitude decay rowSum coercivity
  have hrate : 0 < rate := by
    exact finitePiLpExponentialInverseDecayRate_pos
      hK.1 hdecay hrowSum hcoercivity
  apply finitePiLpExponentialKernelBound_of_tilted_coercive
    dist hsymm hself hrate hcoercivity K C hKC
  intro root
  exact isCoerciveCLM_finitePiLpTiltConj_inverse_canonical
    dist hsymm htri K hdecay hcoercivity hrowSum hK hcoer hexpSum root

end

end YangMills.RG
