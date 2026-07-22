/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395GroupedNeumannDecay

/-!
# Exponential decay of the physical CMP99 patched covariance

The literal parametrix is the regional sum `sum_Pi h_Pi C_Pi h_Pi`.
Although the family of cells grows with the volume, its point-source kernel
has no volume factor: Cauchy--Schwarz and `sum_Pi h_Pi(x)^2 = 1` bound the
sum of the two endpoint cutoffs by one.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

universe v

variable {M Nc Q j : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]
variable {ScaleSite : Fin (j + 2) → Type v}
variable [∀ r, DecidableEq (ScaleSite r)]
variable {Scaled : CMP99SourceScaledStratification
  (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
variable {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
variable {gap : Fin (j + 1) → ℕ}

/-- The two endpoint values of a square partition have total absolute
overlap at most one. -/
theorem cmp99SourceSquarePartition_sum_norm_mul_norm_le_one
    (S : CMP99SourceSquarePartition Q)
    (source target : FinBox 4 (2 * Q)) :
    (∑ cell : FinBox 4 Q,
      ‖S.value cell target‖ * ‖S.value cell source‖) ≤ 1 := by
  classical
  have ht : (∑ cell : FinBox 4 Q, ‖S.value cell target‖ ^ 2) = 1 := by
    simpa [Real.norm_eq_abs, sq_abs] using S.square_sum target
  have hs : (∑ cell : FinBox 4 Q, ‖S.value cell source‖ ^ 2) = 1 := by
    simpa [Real.norm_eq_abs, sq_abs] using S.square_sum source
  calc
    (∑ cell : FinBox 4 Q,
        ‖S.value cell target‖ * ‖S.value cell source‖) ≤
        Real.sqrt (∑ cell : FinBox 4 Q, ‖S.value cell target‖ ^ 2) *
          Real.sqrt (∑ cell : FinBox 4 Q, ‖S.value cell source‖ ^ 2) := by
      simpa only [Finset.sum_attach, Finset.mem_univ, true_and] using
        (Real.sum_mul_le_sqrt_mul_sqrt
          (Finset.univ : Finset (FinBox 4 Q))
          (fun cell ↦ ‖S.value cell target‖)
          (fun cell ↦ ‖S.value cell source‖))
    _ = 1 := by rw [ht, hs]; norm_num

/-- A square-partition localization of uniformly exponentially decaying
operators has the same amplitude and rate as one summand. -/
theorem finitePiLpExponentialKernelBound_squarePartition_sum
    {g : Type*} [NormedAddCommGroup g] [NormedSpace ℝ g]
    [FiniteDimensional ℝ g]
    (S : CMP99SourceSquarePartition Q)
    (C : FinBox 4 Q →
      (FinitePiLpField (FinBox 4 (2 * Q)) g →L[ℝ]
        FinitePiLpField (FinBox 4 (2 * Q)) g))
    (metric : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ)
    {A rate : ℝ}
    (hC : ∀ cell,
      FinitePiLpTypedExponentialKernelBound (C cell) metric A rate) :
    FinitePiLpExponentialKernelBound
      (∑ cell : FinBox 4 Q,
        (finitePiLpScalarMultiplier (g := g) (S.value cell)).comp
          ((C cell).comp
            (finitePiLpScalarMultiplier (g := g) (S.value cell))))
      metric A rate := by
  classical
  have hA : 0 ≤ A := (hC default).1
  have hrate : 0 < rate := (hC default).2.1
  refine ⟨hA, hrate, ?_⟩
  intro source target v
  simp only [ContinuousLinearMap.sum_apply]
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  calc
    ‖∑ cell : FinBox 4 Q,
        (finitePiLpScalarMultiplier (g := g) (S.value cell)).comp
          ((C cell).comp
            (finitePiLpScalarMultiplier (g := g) (S.value cell)))
            (singleFinitePiLp source v) target‖ ≤
        ∑ cell : FinBox 4 Q,
          ‖(finitePiLpScalarMultiplier (g := g) (S.value cell)).comp
            ((C cell).comp
              (finitePiLpScalarMultiplier (g := g) (S.value cell)))
              (singleFinitePiLp source v) target‖ := norm_sum_le _ _
    _ ≤ ∑ cell : FinBox 4 Q,
        (‖S.value cell target‖ * ‖S.value cell source‖) *
          (A * Real.exp (-(rate * (metric target source : ℝ))) * ‖v‖) := by
      apply Finset.sum_le_sum
      intro cell _
      simp only [ContinuousLinearMap.comp_apply,
        finitePiLpScalarMultiplier_apply, finitePiLpScalarMultiplier_single]
      change ‖S.value cell target •
          C cell (singleFinitePiLp source (S.value cell source • v)) target‖ ≤ _
      rw [norm_smul]
      calc
        ‖S.value cell target‖ *
            ‖C cell (singleFinitePiLp source
              (S.value cell source • v)) target‖ ≤
            ‖S.value cell target‖ *
              (A * Real.exp (-(rate * (metric target source : ℝ))) *
                ‖S.value cell source • v‖) :=
          mul_le_mul_of_nonneg_left
            ((hC cell).2.2 source target (S.value cell source • v))
            (norm_nonneg (S.value cell target))
        _ = (‖S.value cell target‖ * ‖S.value cell source‖) *
            (A * Real.exp (-(rate * (metric target source : ℝ))) * ‖v‖) := by
          rw [norm_smul]
          ring
    _ = (∑ cell : FinBox 4 Q,
        ‖S.value cell target‖ * ‖S.value cell source‖) *
          (A * Real.exp (-(rate * (metric target source : ℝ))) * ‖v‖) := by
      rw [Finset.sum_mul]
    _ ≤ A * Real.exp (-(rate * (metric target source : ℝ))) * ‖v‖ := by
      have hoverlap := cmp99SourceSquarePartition_sum_norm_mul_norm_le_one
        S source target
      have hfactor : 0 ≤
          A * Real.exp (-(rate * (metric target source : ℝ))) * ‖v‖ :=
        mul_nonneg (mul_nonneg hA (Real.exp_pos _).le) (norm_nonneg v)
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hoverlap hfactor

namespace CMP99SourceDependentOmegaGeometry

/-- Uniform amplitude of every generated regional covariance in the patched
parametrix. -/
noncomputable def cmp99Eq395PhysicalPatchedCovarianceDecayAmplitude
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  2 / ((cmp99SourceGeneratedPhysicalPrecisionUpperBound
    4 M (depth + 1) spacing epsilon) ^ 2)⁻¹

set_option maxRecDepth 6000 in
set_option maxHeartbeats 5000000 in
/-- The literal patched covariance has the same exponential kernel bound as
one regional covariance.  Square-partition overlap removes the cell sum
exactly, so the amplitude is independent of the ambient volume. -/
theorem cmp99Eq395PhysicalPatchedCovariance_exponentialKernelBound
    (D : (cell : FinBox 4 Q) → CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : ∀ cell, (D cell).fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (P : CMP95SourceSmoothPartitionProfile)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    let C0 : CMP99Eq395AmbientOperator Q Nc :=
      cmp99Eq395PhysicalPatchedCovariance D hpi5 P hM depth hspacing
        background budget fineSmall hsmall
    FinitePiLpExponentialKernelBound C0
      (finBoxDist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ)
      (cmp99Eq395PhysicalPatchedCovarianceDecayAmplitude
        M depth spacing epsilon)
      (cmp99Eq395GeneratedCovarianceDecayRate M depth spacing epsilon) := by
  dsimp only
  classical
  let S := cmp95SourcePeriodicCoarseSquarePartition P Q
  let C := cmp99Eq395PhysicalCovariance D hpi5 hM depth hspacing background
    budget fineSmall hsmall
  let A := cmp99Eq395PhysicalPatchedCovarianceDecayAmplitude
    M depth spacing epsilon
  let rate := cmp99Eq395GeneratedCovarianceDecayRate M depth spacing epsilon
  have hC : ∀ cell,
      FinitePiLpTypedExponentialKernelBound (C cell) finBoxDist A rate := by
    intro cell
    simpa [C, A, rate, cmp99Eq395PhysicalCovariance,
      cmp99Eq395PhysicalPatchedCovarianceDecayAmplitude] using
      ((D cell).generatedPhysicalCoarseCovarianceAmbient_exponentialKernelBound
        (hpi5 cell) (cmp99OmegaPi4Index j) hM depth hspacing background budget
        fineSmall hsmall)
  rw [cmp99Eq395PhysicalPatchedCovariance]
  simpa [S, C, A, rate, cmp99Eq395PhysicalSmoothMultiplier] using
    (finitePiLpExponentialKernelBound_squarePartition_sum S C finBoxDist hC)

/-- Common input rate for composing the patched covariance with its grouped
Neumann inverse. -/
noncomputable def cmp99Eq395PhysicalCorrectedCovarianceInputRate
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  min (cmp99Eq395GeneratedCovarianceDecayRate M depth spacing epsilon)
    (cmp99Eq395PhysicalGroupedNeumannDecayRate M depth spacing epsilon)

/-- Rate retained by the complete corrected covariance after one physical
kernel composition. -/
noncomputable def cmp99Eq395PhysicalCorrectedCovarianceDecayRate
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  cmp99Eq395PhysicalCorrectedCovarianceInputRate M depth spacing epsilon *
    (2 / 3)

/-- Explicit volume-independent amplitude of the complete corrected
covariance. -/
noncomputable def cmp99Eq395PhysicalCorrectedCovarianceDecayAmplitude
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  let ratio := cmp99Eq395PhysicalGroupedNeumannRatio
    M depth spacing epsilon
  let sigma := cmp99Eq395PhysicalCorrectedCovarianceInputRate
    M depth spacing epsilon / 3
  cmp99Eq395PhysicalPatchedCovarianceDecayAmplitude M depth spacing epsilon *
    (1 - ratio)⁻¹ * cmp99OmegaSiteExpSumBound sigma

set_option maxRecDepth 6000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- The exact corrected physical covariance has a single explicit,
volume-independent exponential kernel bound.  Both the cell sum and the
infinite Neumann sum have been consumed internally. -/
theorem cmp99Eq395PhysicalCorrectedCovariance_exponentialKernelBound
    (D : (cell : FinBox 4 Q) → CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : ∀ cell, (D cell).fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (P : CMP95SourceSmoothPartitionProfile)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    (hcontract : cmp99Eq395PhysicalGroupedNeumannRatio
      M depth spacing epsilon < 1) :
    let Ccorr : CMP99Eq395AmbientOperator Q Nc :=
      cmp99Eq395PhysicalCorrectedCovariance D hpi5 P hM depth hspacing
        background budget fineSmall hsmall
    FinitePiLpExponentialKernelBound Ccorr
      (finBoxDist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ)
      (cmp99Eq395PhysicalCorrectedCovarianceDecayAmplitude
        M depth spacing epsilon)
      (cmp99Eq395PhysicalCorrectedCovarianceDecayRate
        M depth spacing epsilon) := by
  dsimp only
  let C0 := cmp99Eq395PhysicalPatchedCovariance D hpi5 P hM depth hspacing
    background budget fineSmall hsmall
  let N : CMP99Eq395AmbientOperator Q Nc := ∑' n : ℕ,
    (cmp99Eq395PhysicalCorrection D hpi5 P hM depth hspacing background
      budget fineSmall hsmall : CMP99Eq395AmbientOperator Q Nc) ^ n
  let patchedRate := cmp99Eq395GeneratedCovarianceDecayRate
    M depth spacing epsilon
  let neumannRate := cmp99Eq395PhysicalGroupedNeumannDecayRate
    M depth spacing epsilon
  let rate := min patchedRate neumannRate
  let sigma := rate / 3
  let S := cmp99OmegaSiteExpSumBound sigma
  have hC0 := cmp99Eq395PhysicalPatchedCovariance_exponentialKernelBound
    D hpi5 P hM depth hspacing background budget fineSmall hsmall
  have hN := cmp99Eq395PhysicalCorrection_tsum_pow_grouped_exponentialKernelBound
    D hpi5 P hM depth hspacing background budget fineSmall hsmall hcontract
  have hrate : 0 < rate := lt_min hC0.2.1 hN.2.1
  have hsigma : 0 < sigma := by dsimp [sigma]; linarith
  have hS : 0 ≤ S := by
    dsimp [S, cmp99OmegaSiteExpSumBound]
    exact tsum_nonneg fun _ ↦ mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  have hC0weak := finitePiLpTypedExponentialKernelBound_mono_rate
    (rate' := rate) hrate (min_le_left _ _) hC0
  have hNweak := finitePiLpTypedExponentialKernelBound_mono_rate
    (rate' := rate) hrate (min_le_right _ _) hN
  have hsum : ∀ target : FinBox 4 (2 * Q),
      ∑ middle : FinBox 4 (2 * Q),
        Real.exp (-(sigma * (finBoxDist target middle : ℝ))) ≤ S := by
    intro target
    simpa [finBoxDist_comm] using
      finBoxDist_exp_sum_le_cmp99OmegaSiteExpSumBound target hsigma
  have hcomp := finitePiLpTypedExponentialKernelBound_comp
    (ι := FinBox 4 (2 * Q)) (κ := FinBox 4 (2 * Q))
    (ν := FinBox 4 (2 * Q)) (g := SUNLieCoord Nc)
    (distLK := finBoxDist) (distKI := finBoxDist) (distLI := finBoxDist)
    (fun target middle source ↦ finBoxDist_triangle target middle source)
    (A := cmp99Eq395PhysicalPatchedCovarianceDecayAmplitude
      M depth spacing epsilon)
    (B := (1 - cmp99Eq395PhysicalGroupedNeumannRatio
      M depth spacing epsilon)⁻¹)
    (rate := rate) (sigma := sigma) (S := S)
    hsigma (by dsimp [sigma]; linarith) hS hsum C0 N hC0weak hNweak
  rw [cmp99Eq395PhysicalCorrectedCovariance_eq_tsum_pow]
  change FinitePiLpExponentialKernelBound (C0.comp N) finBoxDist
    (cmp99Eq395PhysicalCorrectedCovarianceDecayAmplitude
      M depth spacing epsilon)
    (cmp99Eq395PhysicalCorrectedCovarianceDecayRate
      M depth spacing epsilon)
  convert hcomp using 1
  dsimp [cmp99Eq395PhysicalCorrectedCovarianceDecayRate,
    cmp99Eq395PhysicalCorrectedCovarianceInputRate, rate, sigma,
    patchedRate, neumannRate]
  ring

end CMP99SourceDependentOmegaGeometry

end

end YangMills.RG
