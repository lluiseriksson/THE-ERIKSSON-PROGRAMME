/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedSectionCRightFactorNorm
import YangMills.RG.BalabanCMP99SourceGeneratedCoarseCovarianceTransitionWeightedRow

/-!
# Decay of the generated CMP99 Section C right factor

The literal one-sided factor acts between two consecutive generated source
regions inside the same `tilde Pi^5` envelope.  Its volume-independent norm
therefore gives pointwise exponential decay and a rectangular weighted-row
bound at every fixed positive rate.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

universe v

variable {M Nc Q j : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]
variable {cell : FinBox 4 Q}
variable {ScaleSite : Fin (j + 2) → Type v}
variable [∀ r, DecidableEq (ScaleSite r)]
variable {Scaled : CMP99SourceScaledStratification
  (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
variable {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
variable {gap : Fin (j + 1) → ℕ}

/-- Explicit generated right-factor weighted-row amplitude. -/
noncomputable def cmp99SourceGeneratedPhysicalCoarseRightFactorWeightedRowAmplitude
    (M depth : ℕ) (spacing epsilon rate : ℝ) : ℝ :=
  cmp99SourceGeneratedPhysicalCoarseRightFactorNormBound
      M depth spacing epsilon *
    Real.exp ((2 * rate) * ((1 + 2 * 5 : ℕ) : ℝ)) * 20736

namespace CMP99SourceDependentOmegaGeometry

set_option maxRecDepth 3000
set_option maxHeartbeats 6000000

/-- Pointwise exponential decay of the factor that is actually iterated in
the source Section C expansion. -/
theorem generatedPhysicalCoarseRightFactorCoordinates_exponential
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 1)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon rate : ℝ} (hspacing : 0 < spacing)
    (hrate : 0 < rate)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    FinitePiLpTypedExponentialKernelBound
      (D.generatedPhysicalCoarseRightFactorCoordinates hpi5 r hM depth
        hspacing background budget fineSmall hsmall)
      (D.generatedPhysicalCoarseCovarianceTransitionDist hpi5 r)
      (cmp99SourceGeneratedPhysicalCoarseRightFactorNormBound
          M depth spacing epsilon *
        Real.exp (rate * ((1 + 2 * 5 : ℕ) : ℝ))) rate := by
  let F := D.generatedPhysicalCoarseRightFactorCoordinates hpi5 r hM depth
    hspacing background budget fineSmall hsmall
  let sourceDist := D.generatedPhysicalCoarseCovarianceTransitionDist hpi5 r
  have hrange : FinitePiLpTypedFiniteRange F sourceDist (1 + 2 * 5) := by
    intro source target v hfar
    dsimp [sourceDist] at hfar
    have hnear :=
      D.generatedPhysicalCoarseCovarianceTransitionDist_le_pi5 hpi5 r
        target source
    omega
  have hkernel : FinitePiLpTypedKernelBound F (fun _ _ =>
      cmp99SourceGeneratedPhysicalCoarseRightFactorNormBound
        M depth spacing epsilon) := by
    have hentry := finitePiLpTypedKernelBound_const_opNorm F
    have hnorm := D.norm_generatedPhysicalCoarseRightFactorCoordinates_le
      hpi5 r hM depth hspacing background budget fineSmall hsmall
    intro source target v
    exact (hentry source target v).trans
      (mul_le_mul_of_nonneg_right hnorm (norm_nonneg v))
  change FinitePiLpTypedExponentialKernelBound F sourceDist _ rate
  apply finitePiLpTypedExponentialKernelBound_of_finiteRange
  · unfold cmp99SourceGeneratedPhysicalCoarseRightFactorNormBound
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg _))
        (pow_nonneg (Nat.cast_nonneg M) _))
      (inv_nonneg.mpr (inv_nonneg.mpr (sq_nonneg _)))
  · exact hrate
  · exact hrange
  · exact hkernel

/-- Fixed-rate weighted rows for the generated Section C right factor, with
no ambient-volume cardinality. -/
theorem generatedPhysicalCoarseRightFactorCoordinates_weightedRowKernelBound
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 1)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon rate : ℝ} (hspacing : 0 < spacing)
    (hrate : 0 < rate)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    FinitePiLpTypedWeightedRowKernelBound
      (D.generatedPhysicalCoarseRightFactorCoordinates hpi5 r hM depth
        hspacing background budget fineSmall hsmall)
      (D.generatedPhysicalCoarseCovarianceTransitionDist hpi5 r)
      (cmp99SourceGeneratedPhysicalCoarseRightFactorWeightedRowAmplitude
        M depth spacing epsilon rate) rate := by
  let F := D.generatedPhysicalCoarseRightFactorCoordinates hpi5 r hM depth
    hspacing background budget fineSmall hsmall
  let sourceDist := D.generatedPhysicalCoarseCovarianceTransitionDist hpi5 r
  have hpoint : FinitePiLpTypedExponentialKernelBound F sourceDist
      (cmp99SourceGeneratedPhysicalCoarseRightFactorNormBound
          M depth spacing epsilon *
        Real.exp ((2 * rate) * ((1 + 2 * 5 : ℕ) : ℝ)))
      (2 * rate) :=
    D.generatedPhysicalCoarseRightFactorCoordinates_exponential hpi5 r hM
      depth hspacing (by positivity) background budget fineSmall hsmall
  have hcard : Fintype.card (ActiveGaugeRegion.Site
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r))) ≤
      20736 := D.operatorCoarseRegion_site_card_le_pi5 hpi5
        (cmp99OmegaTransitionNextIndex r)
  have hsum : ∀ source,
      ∑ target : ActiveGaugeRegion.Site
          (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r)),
        Real.exp (-(((2 * rate) - rate) *
          (sourceDist target source : ℝ))) ≤ (20736 : ℝ) := by
    intro source
    calc
      ∑ target, Real.exp (-(((2 * rate) - rate) *
          (sourceDist target source : ℝ))) ≤ ∑ _target, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro target _
        rw [Real.exp_le_one_iff]
        have hdist : 0 ≤ (sourceDist target source : ℝ) := by positivity
        nlinarith
      _ = (Fintype.card (ActiveGaugeRegion.Site
          (D.operatorCoarseRegion hpi5
            (cmp99OmegaTransitionNextIndex r))) : ℝ) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      _ ≤ 20736 := by exact_mod_cast hcard
  have hrow := finitePiLpTypedWeightedRowKernelBound_of_exponential
    F sourceDist hrate.le (by norm_num : (0 : ℝ) ≤ 20736) hpoint hsum
  simpa [F, sourceDist,
    cmp99SourceGeneratedPhysicalCoarseRightFactorWeightedRowAmplitude] using
      hrow

end CMP99SourceDependentOmegaGeometry

end
end YangMills.RG
