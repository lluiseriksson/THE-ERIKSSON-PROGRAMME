/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceRegionalCoarseCovarianceDecay

/-!
# The one-sided regional Section C resolvent factor

Printed CMP99 equation (3.97) contains a one-sided coarse-middle mismatch
followed by the coarse covariance on the larger region.  This file exposes
that source-facing core in its native rectangular types.  It does **not** call
the object below the complete factor of (3.97): the printed exterior cutoffs
and partition multipliers still have to be attached literally.
-/

namespace YangMills.RG

noncomputable section

variable {Q M j Nc : ℕ} [NeZero Q] [NeZero M] [NeZero Nc]
variable {cell : FinBox 4 Q}

/-- The one-sided resolvent factor: the physical consecutive coarse-middle
defect followed by the covariance on the larger source region. -/
noncomputable def cmp99OmegaSourcePhysicalOneStepCoarseRightFactor
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :=
  (cmp99OmegaSourcePhysicalOneStepCoarseMiddleTransitionDefect
      Seq r rho U hspacing ha).comp
    (cmp99OmegaSourcePhysicalOneStepCoarseCovariance Seq
      (cmp99OmegaTransitionIndex r) rho U hspacing ha)

/-- Fixed decay rate for the one-sided Section C core. -/
noncomputable def cmp99OmegaSourcePhysicalOneStepCoarseRightFactorDecayRate
    (M : ℕ) (spacing a : ℝ) : ℝ :=
  2 * min
    (cmp99OmegaSourcePhysicalOneStepCoarseCovarianceDecayRate M spacing a)
    (cmp99OmegaSourcePhysicalOneStepCombesThomasRate M spacing a / 12) / 3

/-- Volume-independent amplitude for the one-sided Section C core. -/
noncomputable def cmp99OmegaSourcePhysicalOneStepCoarseRightFactorDecayAmplitude
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
  AD * AC * S

/-- The covariance transition is the small covariance composed with the
one-sided right factor.  This is the exact typed second-resolvent identity. -/
theorem cmp99OmegaSourcePhysicalOneStepCoarseCovariance_transition_eq_comp_rightFactor
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    cmp99OmegaSourcePhysicalOneStepCoarseCovarianceTransition
        Seq r rho U hspacing ha =
      (cmp99OmegaSourcePhysicalOneStepCoarseCovariance Seq
        (cmp99OmegaTransitionNextIndex r) rho U hspacing ha).comp
        (cmp99OmegaSourcePhysicalOneStepCoarseRightFactor
          Seq r rho U hspacing ha) := by
  simpa [cmp99OmegaSourcePhysicalOneStepCoarseRightFactor] using
    cmp99OmegaSourcePhysicalOneStepCoarseCovariance_transition_resolvent
      Seq r rho U hspacing ha

set_option maxHeartbeats 1000000 in
/-- The right factor is literally the rectangular Green-square mismatch from
the source construction, followed on the right by the larger covariance. -/
theorem cmp99OmegaSourcePhysicalOneStepCoarseRightFactor_eq_greenMismatch_comp_covariance
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    cmp99OmegaSourcePhysicalOneStepCoarseRightFactor
        Seq r rho U hspacing ha =
      (-(cmp99OmegaSourcePhysicalOneStepQ Seq
          (cmp99OmegaTransitionNextIndex r) rho U).comp
        ((((cmp99OmegaSourcePhysicalOneStepGreen Seq
              (cmp99OmegaTransitionNextIndex r) rho U hspacing ha).comp
            ((cmp99OmegaSourcePhysicalOneStepGreen Seq
                (cmp99OmegaTransitionNextIndex r) rho U hspacing ha).comp
                (cmp99OmegaTransitionRestriction (M := M) Seq r) -
              (cmp99OmegaTransitionRestriction (M := M) Seq r).comp
                (cmp99OmegaSourcePhysicalOneStepGreen Seq
                  (cmp99OmegaTransitionIndex r) rho U hspacing ha))) +
          (((cmp99OmegaSourcePhysicalOneStepGreen Seq
                (cmp99OmegaTransitionNextIndex r) rho U hspacing ha).comp
              (cmp99OmegaTransitionRestriction (M := M) Seq r) -
            (cmp99OmegaTransitionRestriction (M := M) Seq r).comp
              (cmp99OmegaSourcePhysicalOneStepGreen Seq
                (cmp99OmegaTransitionIndex r) rho U hspacing ha)).comp
            (cmp99OmegaSourcePhysicalOneStepGreen Seq
              (cmp99OmegaTransitionIndex r) rho U hspacing ha))).comp
          (cmp99OmegaSourcePhysicalOneStepTower Seq
            (cmp99OmegaTransitionIndex r) rho U spacing).weightedAdjoint)).comp
        (cmp99OmegaSourcePhysicalOneStepCoarseCovariance Seq
          (cmp99OmegaTransitionIndex r) rho U hspacing ha) := by
  unfold cmp99OmegaSourcePhysicalOneStepCoarseRightFactor
  rw [cmp99OmegaSourcePhysicalOneStepCoarseMiddleTransitionDefect_eq_greenMismatch]
  rfl

set_option maxHeartbeats 1200000 in
/-- The one-sided factor has a fixed physical exponential rate and an explicit
amplitude independent of the ambient volume and of the number of source
scales. -/
theorem cmp99OmegaSourcePhysicalOneStepCoarseRightFactor_exponentialKernelBound
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    FinitePiLpTypedExponentialKernelBound
      (cmp99OmegaSourcePhysicalOneStepCoarseRightFactor
        Seq r rho U hspacing ha)
      (cmp99OmegaCoarseTransitionDist (M := M) Seq r)
      (cmp99OmegaSourcePhysicalOneStepCoarseRightFactorDecayAmplitude
        M spacing a)
      (cmp99OmegaSourcePhysicalOneStepCoarseRightFactorDecayRate
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
  let Cl := cmp99OmegaSourcePhysicalOneStepCoarseCovariance
    Seq largeIndex rho U hspacing ha
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
  have h := finitePiLpTypedExponentialKernelBound_comp
    (cmp99OmegaCoarseTransitionDist (M := M) Seq r)
    (cmp99OmegaCoarseDist (M := M) Seq largeIndex)
    (cmp99OmegaCoarseTransitionDist (M := M) Seq r)
    (fun target middle source =>
      finBoxDist_triangle
        (cmp99OmegaCoarseRepresentative (M := M) Seq
          (cmp99OmegaTransitionNextIndex r) target)
        (cmp99OmegaCoarseRepresentative (M := M) Seq largeIndex middle)
        (cmp99OmegaCoarseRepresentative (M := M) Seq largeIndex source))
    hsigma (by dsimp [sigma]; linarith) hS hsumTransition D Cl hD hCl
  have h' : FinitePiLpTypedExponentialKernelBound (D.comp Cl)
      (cmp99OmegaCoarseTransitionDist (M := M) Seq r)
      (AD * AC * S) (2 * base / 3) := by
    convert h using 1
    ring
  simpa [cmp99OmegaSourcePhysicalOneStepCoarseRightFactor,
    cmp99OmegaSourcePhysicalOneStepCoarseRightFactorDecayRate,
    cmp99OmegaSourcePhysicalOneStepCoarseRightFactorDecayAmplitude,
    mu, theta, base, sigma, AC, AD, S, largeIndex, Cl, D] using h'

end

end YangMills.RG
