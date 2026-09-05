/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedSectionCCutFactor
import YangMills.RG.BalabanCMP99SourceGeneratedSectionCRightFactorDecay

/-!
# Decay of the literal generated CMP99 Section C cut factor

The source cutoffs are contractions and the two generated terminal carriers
lie in the same literal `tilde Pi^5` envelope.  Hence the correctly ordered
cut factor inherits both pointwise exponential decay and a fixed-rate
weighted-row estimate without ambient-volume cardinality.
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

namespace CMP99SourceDependentOmegaGeometry

set_option maxRecDepth 3000
set_option maxHeartbeats 6000000

/-- Pointwise fixed-rate decay of the correctly ordered generated cut factor
in CMP99 (3.97). -/
theorem generatedPhysicalCoarseSectionCCutFactorCoordinates_exponential
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 1))
    (Cuts : D.GeneratedSectionCTransitionCutData hpi5 r)
    (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon rate : ℝ} (hspacing : 0 < spacing) (hrate : 0 < rate)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    FinitePiLpTypedExponentialKernelBound
      (D.generatedPhysicalCoarseSectionCCutFactorCoordinates hpi5 r Cuts hM
        depth hspacing background budget fineSmall hsmall)
      (D.generatedPhysicalCoarseCovarianceTransitionDist hpi5 r)
      (cmp99SourceGeneratedPhysicalCoarseRightFactorNormBound
          M depth spacing epsilon *
        Real.exp (rate * ((1 + 2 * 5 : ℕ) : ℝ))) rate := by
  let F := D.generatedPhysicalCoarseSectionCCutFactorCoordinates hpi5 r Cuts
    hM depth hspacing background budget fineSmall hsmall
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
    have hnorm :=
      D.norm_generatedPhysicalCoarseSectionCCutFactorCoordinates_le hpi5 r
        Cuts hM depth hspacing background budget fineSmall hsmall
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

/-- Volume-independent weighted rows for the literal generated cut factor. -/
theorem generatedPhysicalCoarseSectionCCutFactorCoordinates_weightedRowKernelBound
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 1))
    (Cuts : D.GeneratedSectionCTransitionCutData hpi5 r)
    (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon rate : ℝ} (hspacing : 0 < spacing) (hrate : 0 < rate)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    FinitePiLpTypedWeightedRowKernelBound
      (D.generatedPhysicalCoarseSectionCCutFactorCoordinates hpi5 r Cuts hM
        depth hspacing background budget fineSmall hsmall)
      (D.generatedPhysicalCoarseCovarianceTransitionDist hpi5 r)
      (cmp99SourceGeneratedPhysicalCoarseRightFactorWeightedRowAmplitude
        M depth spacing epsilon rate) rate := by
  let F := D.generatedPhysicalCoarseSectionCCutFactorCoordinates hpi5 r Cuts
    hM depth hspacing background budget fineSmall hsmall
  let sourceDist := D.generatedPhysicalCoarseCovarianceTransitionDist hpi5 r
  have hpoint : FinitePiLpTypedExponentialKernelBound F sourceDist
      (cmp99SourceGeneratedPhysicalCoarseRightFactorNormBound
          M depth spacing epsilon *
        Real.exp ((2 * rate) * ((1 + 2 * 5 : ℕ) : ℝ)))
      (2 * rate) :=
    D.generatedPhysicalCoarseSectionCCutFactorCoordinates_exponential hpi5 r
      Cuts hM depth hspacing (by positivity) background budget fineSmall hsmall
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
