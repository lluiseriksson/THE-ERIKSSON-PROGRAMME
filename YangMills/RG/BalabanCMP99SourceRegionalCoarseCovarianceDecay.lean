/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceRegionalCoarseMiddleDecay

/-!
# Exponential decay of the physical CMP99 coarse covariance

The coarse precision `Q' G'^2 Q'^dagger` is exponentially localized but not
finite range.  This file spends an explicit, volume-independent fraction of
its decay rate in the exponential-kernel Combes--Thomas theorem and obtains
decay of its literal inverse.
-/

namespace YangMills.RG

noncomputable section

variable {Q M j Nc : ℕ} [NeZero Q] [NeZero M] [NeZero Nc]
variable {cell : FinBox 4 Q}

/-- The elementary vanishing estimate used for an exponential tilt. -/
theorem Real.exp_sub_one_le_mul_exp_of_nonneg {x : ℝ} (_hx : 0 ≤ x) :
    Real.exp x - 1 ≤ x * Real.exp x := by
  have hbase := Real.add_one_le_exp (-x)
  have hsmall : 1 - Real.exp (-x) ≤ x := by linarith
  have hmul := mul_le_mul_of_nonneg_left hsmall (Real.exp_pos x).le
  have hinv : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  nlinarith

/-- The exact pointwise tilt weight is dominated by a lower-rate exponential
with a coefficient linear in the tilt. -/
theorem cmp99_exponentialTiltWeight_le
    {rate decay : ℝ} (hrate : 0 ≤ rate) (hdecay : 0 < decay)
    (hrateHalf : rate ≤ decay / 2) (n : ℕ) :
    (Real.exp (rate * (n : ℝ)) - 1) *
        Real.exp (-(decay * (n : ℝ))) ≤
      rate * (4 / decay) *
        Real.exp (-((decay / 4) * (n : ℝ))) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hx : 0 ≤ rate * (n : ℝ) := mul_nonneg hrate hn
  have hfirst := Real.exp_sub_one_le_mul_exp_of_nonneg hx
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
  have hz : 0 ≤ (decay / 4) * (n : ℝ) := by positivity
  have hzexp : (decay / 4) * (n : ℝ) ≤
      Real.exp ((decay / 4) * (n : ℝ)) := by
    linarith [Real.add_one_le_exp ((decay / 4) * (n : ℝ))]
  have hscale : 0 ≤ 4 / decay := by positivity
  have hnexp : (n : ℝ) ≤
      (4 / decay) * Real.exp ((decay / 4) * (n : ℝ)) := by
    have h := mul_le_mul_of_nonneg_left hzexp hscale
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

/-- Canonical coarse-covariance decay rate.  The first branch preserves half
the middle-kernel rate; the second spends at most half of the physical
coercivity after the bilateral Schur sum. -/
noncomputable def cmp99OmegaSourcePhysicalOneStepCoarseCovarianceDecayRate
    (M : ℕ) (spacing a : ℝ) : ℝ :=
  let decay := cmp99OmegaSourcePhysicalOneStepCombesThomasRate M spacing a / 4
  let A := cmp99OmegaSourcePhysicalOneStepCoarseMiddleDecayAmplitude M spacing a
  let S := cmp99OmegaSiteExpSumBound (decay / 4)
  let c := (cmp99OmegaSourcePhysicalOneStepPrecisionUpperBound spacing a ^ 2)⁻¹
  min (decay / 2) (c * decay / (8 * (A * S + 1)))

theorem cmp99OmegaSourcePhysicalOneStepCoarseMiddleDecayAmplitude_nonneg
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    0 ≤ cmp99OmegaSourcePhysicalOneStepCoarseMiddleDecayAmplitude M spacing a := by
  let theta := cmp99OmegaSourcePhysicalOneStepCombesThomasRate M spacing a
  let AG := 2 / cmp99OmegaSourcePhysicalOneStepCoercivityConstant M spacing a
  let S := cmp99OmegaSiteExpSumBound (theta / 12)
  let AQ := Real.exp ((theta / 3) * (M : ℝ))
  let AQdag := (M : ℝ) ^ 2 * Real.exp ((theta / 2) * (M : ℝ))
  have hc := cmp99OmegaSourcePhysicalOneStepCoercivityConstant_pos
    (M := M) (spacing := spacing) ha
  have htheta := cmp99OmegaSourcePhysicalOneStepCombesThomasRate_pos
    (M := M) hspacing ha
  have hS : 0 ≤ S := by
    dsimp [S, cmp99OmegaSiteExpSumBound]
    exact tsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _)
      (Real.exp_pos _).le
  change 0 ≤ AQ * (AG * (AG * AQdag * S) * S) * S
  dsimp [AQ, AG, AQdag]
  positivity

theorem cmp99OmegaSourcePhysicalOneStepCoarseCovarianceDecayRate_pos
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    0 < cmp99OmegaSourcePhysicalOneStepCoarseCovarianceDecayRate M spacing a := by
  let decay := cmp99OmegaSourcePhysicalOneStepCombesThomasRate M spacing a / 4
  let A := cmp99OmegaSourcePhysicalOneStepCoarseMiddleDecayAmplitude M spacing a
  let S := cmp99OmegaSiteExpSumBound (decay / 4)
  let c := (cmp99OmegaSourcePhysicalOneStepPrecisionUpperBound spacing a ^ 2)⁻¹
  have hdecay : 0 < decay := by
    dsimp [decay]
    positivity [cmp99OmegaSourcePhysicalOneStepCombesThomasRate_pos
      (M := M) hspacing ha]
  have hA : 0 ≤ A := by
    exact cmp99OmegaSourcePhysicalOneStepCoarseMiddleDecayAmplitude_nonneg
      hspacing ha
  have hS : 0 ≤ S := by
    dsimp [S, cmp99OmegaSiteExpSumBound]
    exact tsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _)
      (Real.exp_pos _).le
  have hc : 0 < c := by
    dsimp [c]
    positivity [cmp99OmegaSourcePhysicalOneStepPrecisionUpperBound_pos
      (a := a) hspacing]
  unfold cmp99OmegaSourcePhysicalOneStepCoarseCovarianceDecayRate
  dsimp [decay, A, S, c]
  exact lt_min (by positivity) (by positivity)

set_option maxHeartbeats 1200000 in
/-- The canonical rate consumes at most half the physical coarse-middle
coercivity. -/
theorem cmp99OmegaSourcePhysicalOneStepCoarseCovarianceDecayRate_budget
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    let decay := cmp99OmegaSourcePhysicalOneStepCombesThomasRate M spacing a / 4
    let A := cmp99OmegaSourcePhysicalOneStepCoarseMiddleDecayAmplitude M spacing a
    let S := cmp99OmegaSiteExpSumBound (decay / 4)
    let c := (cmp99OmegaSourcePhysicalOneStepPrecisionUpperBound spacing a ^ 2)⁻¹
    let rate := cmp99OmegaSourcePhysicalOneStepCoarseCovarianceDecayRate M spacing a
    A * (rate * (4 / decay) * S) ≤ c / 2 := by
  dsimp only
  let decay := cmp99OmegaSourcePhysicalOneStepCombesThomasRate M spacing a / 4
  let A := cmp99OmegaSourcePhysicalOneStepCoarseMiddleDecayAmplitude M spacing a
  let S := cmp99OmegaSiteExpSumBound (decay / 4)
  let c := (cmp99OmegaSourcePhysicalOneStepPrecisionUpperBound spacing a ^ 2)⁻¹
  let rate := cmp99OmegaSourcePhysicalOneStepCoarseCovarianceDecayRate M spacing a
  have hdecay : 0 < decay := by
    dsimp [decay]
    positivity [cmp99OmegaSourcePhysicalOneStepCombesThomasRate_pos
      (M := M) hspacing ha]
  have hA : 0 ≤ A :=
    cmp99OmegaSourcePhysicalOneStepCoarseMiddleDecayAmplitude_nonneg hspacing ha
  have hS : 0 ≤ S := by
    dsimp [S, cmp99OmegaSiteExpSumBound]
    exact tsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _)
      (Real.exp_pos _).le
  have hc : 0 < c := by
    dsimp [c]
    positivity [cmp99OmegaSourcePhysicalOneStepPrecisionUpperBound_pos
      (a := a) hspacing]
  have hrate : rate ≤ c * decay / (8 * (A * S + 1)) := by
    dsimp [rate, cmp99OmegaSourcePhysicalOneStepCoarseCovarianceDecayRate]
    exact min_le_right _ _
  have hden : 0 < A * S + 1 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hrate
    (show 0 ≤ (4 / decay) * (A * S) by positivity)
  have hquot : (A * S) / (A * S + 1) ≤ 1 := by
    apply (div_le_one hden).2
    linarith
  have hcalc :
      (c * decay / (8 * (A * S + 1))) *
          ((4 / decay) * (A * S)) =
        c / 2 * ((A * S) / (A * S + 1)) := by
    field_simp
    ring
  calc
    A * (rate * (4 / decay) * S) =
        rate * ((4 / decay) * (A * S)) := by ring
    _ ≤ (c * decay / (8 * (A * S + 1))) *
        ((4 / decay) * (A * S)) := hmul
    _ = c / 2 * ((A * S) / (A * S + 1)) := hcalc
    _ ≤ c / 2 * 1 :=
      mul_le_mul_of_nonneg_left hquot (by positivity)
    _ = c / 2 := by ring

set_option maxHeartbeats 1200000 in
/-- C4 for the literal physical coarse covariance: its inverse decay follows
from the exponentially localized middle operator, its source-generated
coercivity, and the canonical volume-independent tilt budget. -/
theorem cmp99OmegaSourcePhysicalOneStepCoarseCovariance_exponentialKernelBound
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    FinitePiLpExponentialKernelBound
      (cmp99OmegaSourcePhysicalOneStepCoarseCovariance
        Seq r rho U hspacing ha)
      (cmp99OmegaCoarseDist (M := M) Seq r)
      (2 / (cmp99OmegaSourcePhysicalOneStepPrecisionUpperBound spacing a ^ 2)⁻¹)
      (cmp99OmegaSourcePhysicalOneStepCoarseCovarianceDecayRate M spacing a) := by
  let decay := cmp99OmegaSourcePhysicalOneStepCombesThomasRate M spacing a / 4
  let A := cmp99OmegaSourcePhysicalOneStepCoarseMiddleDecayAmplitude M spacing a
  let S := cmp99OmegaSiteExpSumBound (decay / 4)
  let c := (cmp99OmegaSourcePhysicalOneStepPrecisionUpperBound spacing a ^ 2)⁻¹
  let rate := cmp99OmegaSourcePhysicalOneStepCoarseCovarianceDecayRate M spacing a
  have hdecay : 0 < decay := by
    dsimp [decay]
    positivity [cmp99OmegaSourcePhysicalOneStepCombesThomasRate_pos
      (M := M) hspacing ha]
  have hrate : 0 < rate :=
    cmp99OmegaSourcePhysicalOneStepCoarseCovarianceDecayRate_pos hspacing ha
  have hrateHalf : rate ≤ decay / 2 := by
    dsimp [rate, cmp99OmegaSourcePhysicalOneStepCoarseCovarianceDecayRate]
    exact min_le_left _ _
  have hS : 0 ≤ S := by
    dsimp [S, cmp99OmegaSiteExpSumBound]
    exact tsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _)
      (Real.exp_pos _).le
  have hc : 0 < c := by
    dsimp [c]
    positivity [cmp99OmegaSourcePhysicalOneStepPrecisionUpperBound_pos
      (a := a) hspacing]
  have hsum : ∀ target,
      ∑ source,
        (Real.exp (rate *
            (cmp99OmegaCoarseDist (M := M) Seq r target source : ℝ)) - 1) *
          Real.exp (-(decay *
            (cmp99OmegaCoarseDist (M := M) Seq r target source : ℝ))) ≤
        rate * (4 / decay) * S := by
    intro target
    calc
      ∑ source,
          (Real.exp (rate *
              (cmp99OmegaCoarseDist (M := M) Seq r target source : ℝ)) - 1) *
            Real.exp (-(decay *
              (cmp99OmegaCoarseDist (M := M) Seq r target source : ℝ))) ≤
        ∑ source, rate * (4 / decay) *
          Real.exp (-((decay / 4) *
            (cmp99OmegaCoarseDist (M := M) Seq r target source : ℝ))) :=
          Finset.sum_le_sum (fun source _ =>
            cmp99_exponentialTiltWeight_le hrate.le hdecay hrateHalf _)
      _ = (rate * (4 / decay)) *
          ∑ source, Real.exp (-((decay / 4) *
            (cmp99OmegaCoarseDist (M := M) Seq r target source : ℝ))) := by
        rw [Finset.mul_sum]
      _ ≤ (rate * (4 / decay)) * S :=
        mul_le_mul_of_nonneg_left
          (cmp99OmegaCoarseDist_exp_sum_le Seq r target (by positivity))
          (by positivity)
      _ = rate * (4 / decay) * S := by ring
  apply finitePiLpExponentialKernelBound_inverse_of_exponential
    (cmp99OmegaCoarseDist (M := M) Seq r)
    (fun p q => by simp [cmp99OmegaCoarseDist, finBoxDist_comm])
    (fun p q s => by
      exact finBoxDist_triangle
        (cmp99OmegaCoarseRepresentative (M := M) Seq r p)
        (cmp99OmegaCoarseRepresentative (M := M) Seq r q)
        (cmp99OmegaCoarseRepresentative (M := M) Seq r s))
    (fun p => by simp [cmp99OmegaCoarseDist, finBoxDist_self])
    hrate hc (mul_nonneg (by positivity) hS)
    (cmp99OmegaSourcePhysicalOneStepCoarseCovarianceMiddle
      Seq r rho U hspacing ha)
    (cmp99OmegaSourcePhysicalOneStepCoarseCovariance
      Seq r rho U hspacing ha)
    (cmp99OmegaSourcePhysicalOneStepCoarseCovarianceMiddle_exponentialKernelBound
      Seq r rho U hspacing ha)
    (coercive_cmp99OmegaSourcePhysicalOneStepCoarseCovarianceMiddle
      Seq r rho U hspacing ha)
    (cmp99OmegaSourcePhysicalOneStepMiddle_comp_coarseCovariance
      Seq r rho U hspacing ha)
    hsum
  simpa [decay, A, S, c, rate] using
    cmp99OmegaSourcePhysicalOneStepCoarseCovarianceDecayRate_budget
      (M := M) hspacing ha

/-- Fixed rate for a consecutive coarse-covariance transition. -/
noncomputable def
    cmp99OmegaSourcePhysicalOneStepCoarseCovarianceTransitionDecayRate
    (M : ℕ) (spacing a : ℝ) : ℝ :=
  min (cmp99OmegaSourcePhysicalOneStepCoarseCovarianceDecayRate M spacing a)
      (cmp99OmegaSourcePhysicalOneStepCombesThomasRate M spacing a / 12) / 3

/-- Explicit amplitude after the two typed compositions in the second
resolvent identity. -/
noncomputable def
    cmp99OmegaSourcePhysicalOneStepCoarseCovarianceTransitionDecayAmplitude
    (M : ℕ) (spacing a : ℝ) : ℝ :=
  let base := min
    (cmp99OmegaSourcePhysicalOneStepCoarseCovarianceDecayRate M spacing a)
    (cmp99OmegaSourcePhysicalOneStepCombesThomasRate M spacing a / 12)
  let AC := 2 /
    (cmp99OmegaSourcePhysicalOneStepPrecisionUpperBound spacing a ^ 2)⁻¹
  let AD :=
    cmp99OmegaSourcePhysicalOneStepCoarseMiddleTransitionDecayAmplitude
      M spacing a
  let S := cmp99OmegaSiteExpSumBound (base / 3)
  AC * (AD * AC * S) * S

set_option maxHeartbeats 1200000 in
/-- C4 for the literal consecutive coarse-covariance mismatch.  All three
operators in the second-resolvent identity are physical and every rectangular
composition is performed in its native regional carrier. -/
theorem cmp99OmegaSourcePhysicalOneStepCoarseCovariance_transition_exponentialKernelBound
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    FinitePiLpTypedExponentialKernelBound
      (cmp99OmegaSourcePhysicalOneStepCoarseCovarianceTransition
        Seq r rho U hspacing ha)
      (cmp99OmegaCoarseTransitionDist (M := M) Seq r)
      (cmp99OmegaSourcePhysicalOneStepCoarseCovarianceTransitionDecayAmplitude
        M spacing a)
      (cmp99OmegaSourcePhysicalOneStepCoarseCovarianceTransitionDecayRate
        M spacing a) := by
  let mu := cmp99OmegaSourcePhysicalOneStepCoarseCovarianceDecayRate M spacing a
  let theta := cmp99OmegaSourcePhysicalOneStepCombesThomasRate M spacing a
  let base := min mu (theta / 12)
  let sigma := base / 3
  let AC := 2 /
    (cmp99OmegaSourcePhysicalOneStepPrecisionUpperBound spacing a ^ 2)⁻¹
  let AD := cmp99OmegaSourcePhysicalOneStepCoarseMiddleTransitionDecayAmplitude
    M spacing a
  let S := cmp99OmegaSiteExpSumBound sigma
  let largeIndex := cmp99OmegaTransitionIndex r
  let smallIndex := cmp99OmegaTransitionNextIndex r
  let Cl := cmp99OmegaSourcePhysicalOneStepCoarseCovariance
    Seq largeIndex rho U hspacing ha
  let Cs := cmp99OmegaSourcePhysicalOneStepCoarseCovariance
    Seq smallIndex rho U hspacing ha
  let D := cmp99OmegaSourcePhysicalOneStepCoarseMiddleTransitionDefect
    Seq r rho U hspacing ha
  have hmu : 0 < mu :=
    cmp99OmegaSourcePhysicalOneStepCoarseCovarianceDecayRate_pos hspacing ha
  have htheta : 0 < theta :=
    cmp99OmegaSourcePhysicalOneStepCombesThomasRate_pos hspacing ha
  have hbase : 0 < base := lt_min hmu (by positivity)
  have hsigma : 0 < sigma := by positivity
  have hS : 0 ≤ S := by
    dsimp [S, cmp99OmegaSiteExpSumBound]
    exact tsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _)
      (Real.exp_pos _).le
  have hCl0 : FinitePiLpTypedExponentialKernelBound Cl
      (cmp99OmegaCoarseDist (M := M) Seq largeIndex) AC mu :=
    finitePiLpTypedExponentialKernelBound_of_square
      (cmp99OmegaSourcePhysicalOneStepCoarseCovariance_exponentialKernelBound
        Seq largeIndex rho U hspacing ha)
  have hCs0 : FinitePiLpTypedExponentialKernelBound Cs
      (cmp99OmegaCoarseDist (M := M) Seq smallIndex) AC mu :=
    finitePiLpTypedExponentialKernelBound_of_square
      (cmp99OmegaSourcePhysicalOneStepCoarseCovariance_exponentialKernelBound
        Seq smallIndex rho U hspacing ha)
  have hD0 : FinitePiLpTypedExponentialKernelBound D
      (cmp99OmegaCoarseTransitionDist (M := M) Seq r) AD (theta / 12) :=
    cmp99OmegaSourcePhysicalOneStepCoarseMiddleTransitionDefect_exponentialKernelBound
      Seq r rho U hspacing ha
  have hCl : FinitePiLpTypedExponentialKernelBound Cl
      (cmp99OmegaCoarseDist (M := M) Seq largeIndex) AC base :=
    finitePiLpTypedExponentialKernelBound_mono_rate hbase (min_le_left _ _) hCl0
  have hD : FinitePiLpTypedExponentialKernelBound D
      (cmp99OmegaCoarseTransitionDist (M := M) Seq r) AD base :=
    finitePiLpTypedExponentialKernelBound_mono_rate hbase (min_le_right _ _) hD0
  have hsumTransition : ∀ target,
      ∑ middle, Real.exp (-(sigma *
        (cmp99OmegaCoarseTransitionDist (M := M) Seq r target middle : ℝ))) ≤ S := by
    intro target
    exact cmp99OmegaCoarseTransitionDist_exp_sum_le Seq r target hsigma
  have hDCl : FinitePiLpTypedExponentialKernelBound (D.comp Cl)
      (cmp99OmegaCoarseTransitionDist (M := M) Seq r)
      (AD * AC * S) (2 * base / 3) := by
    have h := finitePiLpTypedExponentialKernelBound_comp
      (cmp99OmegaCoarseTransitionDist (M := M) Seq r)
      (cmp99OmegaCoarseDist (M := M) Seq largeIndex)
      (cmp99OmegaCoarseTransitionDist (M := M) Seq r)
      (fun target middle source =>
        finBoxDist_triangle
          (cmp99OmegaCoarseRepresentative (M := M) Seq smallIndex target)
          (cmp99OmegaCoarseRepresentative (M := M) Seq largeIndex middle)
          (cmp99OmegaCoarseRepresentative (M := M) Seq largeIndex source))
      hsigma (by dsimp [sigma]; linarith) hS hsumTransition D Cl hD hCl
    convert h using 1 <;> ring
  have hCs : FinitePiLpTypedExponentialKernelBound Cs
      (cmp99OmegaCoarseDist (M := M) Seq smallIndex) AC (2 * base / 3) :=
    finitePiLpTypedExponentialKernelBound_mono_rate
      (by positivity) (by
        have := min_le_left mu (theta / 12)
        dsimp [base]
        nlinarith) hCs0
  have hsumSmall : ∀ target,
      ∑ middle, Real.exp (-(sigma *
        (cmp99OmegaCoarseDist (M := M) Seq smallIndex target middle : ℝ))) ≤ S := by
    intro target
    exact cmp99OmegaCoarseDist_exp_sum_le Seq smallIndex target hsigma
  have hFinal : FinitePiLpTypedExponentialKernelBound (Cs.comp (D.comp Cl))
      (cmp99OmegaCoarseTransitionDist (M := M) Seq r)
      (AC * (AD * AC * S) * S) (base / 3) := by
    have h := finitePiLpTypedExponentialKernelBound_comp
      (cmp99OmegaCoarseDist (M := M) Seq smallIndex)
      (cmp99OmegaCoarseTransitionDist (M := M) Seq r)
      (cmp99OmegaCoarseTransitionDist (M := M) Seq r)
      (fun target middle source =>
        finBoxDist_triangle
          (cmp99OmegaCoarseRepresentative (M := M) Seq smallIndex target)
          (cmp99OmegaCoarseRepresentative (M := M) Seq smallIndex middle)
          (cmp99OmegaCoarseRepresentative (M := M) Seq largeIndex source))
      hsigma (by dsimp [sigma]; linarith) hS hsumSmall Cs (D.comp Cl)
      hCs hDCl
    convert h using 1 <;> ring
  rw [cmp99OmegaSourcePhysicalOneStepCoarseCovariance_transition_resolvent]
  simpa [cmp99OmegaSourcePhysicalOneStepCoarseCovarianceTransitionDecayRate,
    cmp99OmegaSourcePhysicalOneStepCoarseCovarianceTransitionDecayAmplitude,
    mu, theta, base, sigma, AC, AD, S, largeIndex, smallIndex, Cl, Cs, D]
    using hFinal

end

end YangMills.RG
