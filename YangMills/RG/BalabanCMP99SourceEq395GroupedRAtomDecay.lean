/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395RegionalCovarianceDecay

/-!
# Fixed-rate decay of the complete grouped CMP99 (3.95) atom

The exact cellwise cancellation writes the sum of the three printed species
as the negative grouped left defect, followed by the literal regional
covariance and the smooth cutoff.  The two independently established
fixed-rate bounds are composed here with one uniform physical shell sum.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

universe v

variable {M Nc Q j : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]
variable {ScaleSite : Fin (j + 2) → Type v}
variable [∀ r, DecidableEq (ScaleSite r)]
variable {Scaled : CMP99SourceScaledStratification
  (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
variable {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
variable {gap : Fin (j + 1) → ℕ}

namespace CMP99SourceDependentOmegaGeometry

/-- Common input rate used to compose the grouped left defect with the
generated regional covariance. -/
noncomputable def cmp99Eq395PhysicalGroupedRAtomInputRate
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  min (cmp99SourceGeneratedCombesThomasRate
      4 M depth spacing epsilon / 12)
    (cmp99Eq395GeneratedCovarianceDecayRate M depth spacing epsilon)

/-- Rate remaining after the single covariance composition. -/
noncomputable def cmp99Eq395PhysicalGroupedRAtomDecayRate
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  cmp99Eq395PhysicalGroupedRAtomInputRate M depth spacing epsilon * (2 / 3)

/-- Explicit amplitude of the complete grouped physical atom. -/
noncomputable def cmp99Eq395PhysicalGroupedRAtomDecayAmplitude
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  let leftAmplitude :=
    cmp99Eq395PhysicalGlobalRegionalMiddleDecayAmplitude
        M depth spacing epsilon +
      2 * cmp99Eq395GeneratedMiddleDecayAmplitude M depth spacing epsilon
  let coercivity := ((cmp99SourceGeneratedPhysicalPrecisionUpperBound
    4 M (depth + 1) spacing epsilon) ^ 2)⁻¹
  let sigma := cmp99Eq395PhysicalGroupedRAtomInputRate
    M depth spacing epsilon / 3
  leftAmplitude * (2 / coercivity) * cmp99OmegaSiteExpSumBound sigma

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
/-- The complete grouped atom in the physical cell identity has a single
volume-independent exponential kernel bound.  No bound on the atom itself is
assumed: it is derived from the exact factorization `-L * C * h`. -/
theorem cmp99Eq395PhysicalGroupedRAtom_exponentialKernelBound
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
    (cell : FinBox 4 Q) :
    let R : CMP99Eq395AmbientOperator Q Nc :=
      cmp99Eq395PhysicalGroupedRAtom D hpi5 P hM depth hspacing background
        budget fineSmall hsmall cell
    FinitePiLpTypedExponentialKernelBound
      R
      (finBoxDist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ)
      (cmp99Eq395PhysicalGroupedRAtomDecayAmplitude
        M depth spacing epsilon)
      (cmp99Eq395PhysicalGroupedRAtomDecayRate
        M depth spacing epsilon) := by
  dsimp only
  let L := cmp99Eq395PhysicalGroupedLeftDefect D hpi5 P hM depth hspacing
    background budget fineSmall hsmall cell
  let C := cmp99Eq395PhysicalCovariance D hpi5 hM depth hspacing background
    budget fineSmall hsmall cell
  let f := fun block : FinBox 4 (2 * Q) ↦
    (cmp95SourcePeriodicCoarseSquarePartition P Q).value cell block
  let leftRate := cmp99SourceGeneratedCombesThomasRate
    4 M depth spacing epsilon / 12
  let covarianceRate :=
    cmp99Eq395GeneratedCovarianceDecayRate M depth spacing epsilon
  let rate := min leftRate covarianceRate
  let sigma := rate / 3
  let S := cmp99OmegaSiteExpSumBound sigma
  have hL := cmp99Eq395PhysicalGroupedLeftDefect_exponentialKernelBound
    D hpi5 P hM depth hspacing background budget fineSmall hsmall cell
  have hC : FinitePiLpTypedExponentialKernelBound C
      (finBoxDist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ)
      (2 / ((cmp99SourceGeneratedPhysicalPrecisionUpperBound
        4 M (depth + 1) spacing epsilon) ^ 2)⁻¹)
      covarianceRate := by
    simpa [C, cmp99Eq395PhysicalCovariance, covarianceRate] using
      ((D cell).generatedPhysicalCoarseCovarianceAmbient_exponentialKernelBound
        (hpi5 cell) (cmp99OmegaPi4Index j) hM depth hspacing background budget
        fineSmall hsmall)
  have hrate : 0 < rate := lt_min hL.2.1 hC.2.1
  have hsigma : 0 < sigma := by dsimp [sigma]; linarith
  have hS : 0 ≤ S := by
    dsimp [S, cmp99OmegaSiteExpSumBound]
    exact tsum_nonneg fun _ ↦ mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  have hLweak := finitePiLpTypedExponentialKernelBound_mono_rate
    (rate' := rate)
    hrate (min_le_left _ _) hL
  have hCweak := finitePiLpTypedExponentialKernelBound_mono_rate
    (rate' := rate)
    hrate (min_le_right _ _) hC
  have hsum : ∀ target : FinBox 4 (2 * Q),
      ∑ middle : FinBox 4 (2 * Q),
        Real.exp (-(sigma * (finBoxDist target middle : ℝ))) ≤ S := by
    intro target
    simpa [finBoxDist_comm] using
      finBoxDist_exp_sum_le_cmp99OmegaSiteExpSumBound target hsigma
  have hLC := finitePiLpTypedExponentialKernelBound_comp
    (ι := FinBox 4 (2 * Q)) (κ := FinBox 4 (2 * Q))
    (ν := FinBox 4 (2 * Q)) (g := SUNLieCoord Nc)
    (distLK := finBoxDist) (distKI := finBoxDist) (distLI := finBoxDist)
    (fun target middle source ↦ finBoxDist_triangle target middle source)
    (A := cmp99Eq395PhysicalGlobalRegionalMiddleDecayAmplitude
        M depth spacing epsilon +
      2 * cmp99Eq395GeneratedMiddleDecayAmplitude M depth spacing epsilon)
    (B := 2 / ((cmp99SourceGeneratedPhysicalPrecisionUpperBound
      4 M (depth + 1) spacing epsilon) ^ 2)⁻¹)
    (rate := rate) (sigma := sigma) (S := S)
    hsigma (by dsimp [sigma]; linarith) hS hsum (-L) C
    (finitePiLpTypedExponentialKernelBound_neg hLweak) hCweak
  have hf : ∀ block, ‖f block‖ ≤ 1 := fun block ↦
    (cmp95SourcePeriodicCoarseSquarePartition P Q).norm_value_le_one cell block
  have htail := finitePiLpTypedExponentialKernelBound_comp_scalarMultiplier_right
    (ι := FinBox 4 (2 * Q)) (κ := FinBox 4 (2 * Q))
    (g := SUNLieCoord Nc) f ((-L).comp C) hf hLC
  rw [cmp99Eq395PhysicalGroupedRAtom_eq_neg_defect_comp_tail]
  change FinitePiLpTypedExponentialKernelBound
    (((-L).comp C).comp (finitePiLpScalarMultiplier (g := SUNLieCoord Nc) f))
    finBoxDist
    (cmp99Eq395PhysicalGroupedRAtomDecayAmplitude M depth spacing epsilon)
    (cmp99Eq395PhysicalGroupedRAtomDecayRate M depth spacing epsilon)
  convert htail using 1
  dsimp [cmp99Eq395PhysicalGroupedRAtomDecayRate,
    cmp99Eq395PhysicalGroupedRAtomInputRate, rate, sigma, leftRate,
    covarianceRate]
  ring

end CMP99SourceDependentOmegaGeometry

end

end YangMills.RG
