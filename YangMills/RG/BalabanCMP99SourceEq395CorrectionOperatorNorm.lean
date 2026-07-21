/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395CorrectionNeumannDecay
import YangMills.RG.BalabanCMP99SourceEq395Neumann
import YangMills.RG.FinitePiLpScalarCommutator

/-!
# Volume-independent operator contraction for CMP99 equation (3.95)

The fixed-rate kernel estimate and the uniform periodic-box exponential sum
feed the bilateral block Schur test.  This replaces the abstract operator-norm
premise of the physical inverse theorem by one explicit scalar inequality.
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

/-- Explicit Schur amplitude of the complete physical correction. -/
noncomputable def cmp99Eq395PhysicalCorrectionSchurAmplitude
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  cmp99Eq395PhysicalCorrectionSharpWeightedRowAmplitude M depth spacing epsilon *
    cmp99OmegaSiteExpSumBound
      (cmp99Eq395FirstAtomDecayRate M depth spacing epsilon)

/-- The polynomial-shell exponential sum contains its radius-zero term. -/
theorem one_le_cmp99OmegaSiteExpSumBound {sigma : ℝ} (hsigma : 0 < sigma) :
    1 ≤ cmp99OmegaSiteExpSumBound sigma := by
  have hsum := summable_cmp99OmegaSiteExpSumBound hsigma
  have hnonneg : ∀ k : ℕ,
      0 ≤ (((2 * k + 1) ^ 4 : ℕ) : ℝ) *
        Real.exp (-(sigma * (k : ℝ))) := fun k =>
    mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  calc
    1 = ∑ k ∈ ({0} : Finset ℕ),
        (((2 * k + 1) ^ 4 : ℕ) : ℝ) *
          Real.exp (-(sigma * (k : ℝ))) := by norm_num
    _ ≤ ∑' k : ℕ, (((2 * k + 1) ^ 4 : ℕ) : ℝ) *
          Real.exp (-(sigma * (k : ℝ))) :=
      hsum.sum_le_tsum {0} (fun k _ => hnonneg k)
    _ = cmp99OmegaSiteExpSumBound sigma := rfl

namespace CMP99SourceDependentOmegaGeometry

/-- Schur smallness implies the smaller point-kernel contraction used by the
fixed-source Neumann estimate. -/
theorem cmp99Eq395PhysicalCorrectionWeightedRowAmplitude_lt_one_of_schurSmall
    (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    (hschur : cmp99Eq395PhysicalCorrectionSchurAmplitude
      M depth spacing epsilon < 1) :
    cmp99Eq395PhysicalCorrectionSharpWeightedRowAmplitude
      M depth spacing epsilon < 1 := by
  let A := cmp99Eq395PhysicalCorrectionSharpWeightedRowAmplitude
    M depth spacing epsilon
  let rate := cmp99Eq395FirstAtomDecayRate M depth spacing epsilon
  let S := cmp99OmegaSiteExpSumBound rate
  have hrate : 0 < rate := by
    dsimp [rate, cmp99Eq395FirstAtomDecayRate]
    have := cmp99SourceGeneratedCombesThomasRate_pos
      4 M depth hspacing hsmall
    positivity
  have hS : 1 ≤ S := one_le_cmp99OmegaSiteExpSumBound hrate
  by_cases hAle : A ≤ 0
  · exact hAle.trans_lt zero_lt_one
  have hA0 : 0 ≤ A := (lt_of_not_ge hAle).le
  have hAA : A ≤ A * S := by
    calc
      A = A * 1 := (mul_one A).symm
      _ ≤ A * S := mul_le_mul_of_nonneg_left hS hA0
  exact hAA.trans_lt (by
    simpa [A, S, rate, cmp99Eq395PhysicalCorrectionSchurAmplitude] using hschur)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- The literal correction in (3.95) has a volume-independent operator norm
bounded by its explicit fixed-rate Schur amplitude. -/
theorem norm_cmp99Eq395PhysicalCorrection_le_schurAmplitude
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
    ‖cmp99Eq395PhysicalCorrection D hpi5 P hM depth hspacing background
      budget fineSmall hsmall‖ ≤
      cmp99Eq395PhysicalCorrectionSchurAmplitude M depth spacing epsilon := by
  let R := cmp99Eq395PhysicalCorrection D hpi5 P hM depth hspacing background
    budget fineSmall hsmall
  let A := cmp99Eq395PhysicalCorrectionSharpWeightedRowAmplitude
    M depth spacing epsilon
  let rate := cmp99Eq395FirstAtomDecayRate M depth spacing epsilon
  let S := cmp99OmegaSiteExpSumBound rate
  have hrow := cmp99Eq395PhysicalCorrection_sharp_weightedRow D hpi5 P hM depth
    hspacing background budget fineSmall hsmall
  have hrate : 0 < rate := by
    dsimp [rate, cmp99Eq395FirstAtomDecayRate]
    have := cmp99SourceGeneratedCombesThomasRate_pos
      4 M depth hspacing hsmall
    positivity
  have hkernel : FinitePiLpExponentialKernelBound
      (R : CMP99Eq395AmbientOperator Q Nc)
      (finBoxDist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ) A rate := by
    exact finitePiLpTypedExponentialKernelBound_of_weightedRow
      R finBoxDist hrate hrow
  have hS : 0 ≤ S := by
    dsimp [S, cmp99OmegaSiteExpSumBound]
    exact tsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _)
      (Real.exp_pos _).le
  have hsum : ∀ source : FinBox 4 (2 * Q),
      ∑ target : FinBox 4 (2 * Q),
        Real.exp (-(rate * (finBoxDist source target : ℝ))) ≤ S := by
    intro source
    simpa [finBoxDist_comm] using
      (finBoxDist_exp_sum_le_cmp99OmegaSiteExpSumBound
        (Q := Q) source hrate)
  simpa [R, A, rate, S, cmp99Eq395PhysicalCorrectionSchurAmplitude] using
    (finitePiLpOpNorm_le_of_exponentialKernelBound R finBoxDist
      (fun x y => finBoxDist_comm x y) hS hkernel hsum)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- The physical corrected covariance is an exact right inverse once the
explicit, volume-independent Schur amplitude is smaller than one. -/
theorem cmp99Eq395PhysicalGlobalMiddle_comp_correctedCovariance_eq_id_of_schurSmall
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
    (hschur : cmp99Eq395PhysicalCorrectionSchurAmplitude
      M depth spacing epsilon < 1) :
    (cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background budget
      fineSmall hsmall).comp
        (cmp99Eq395PhysicalCorrectedCovariance D hpi5 P hM depth hspacing
          background budget fineSmall hsmall) =
      ContinuousLinearMap.id ℝ
        (GaugeZeroCochain 4 (2 * Q) (SUNLieCoord Nc)) := by
  apply cmp99Eq395PhysicalGlobalMiddle_comp_correctedCovariance_eq_id
  exact (norm_cmp99Eq395PhysicalCorrection_le_schurAmplitude D hpi5 P hM
    depth hspacing background budget fineSmall hsmall).trans_lt hschur

end CMP99SourceDependentOmegaGeometry
end
end YangMills.RG
