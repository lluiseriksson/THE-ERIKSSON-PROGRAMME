/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedCoarseCovarianceTransitionDecay
import YangMills.RG.FinitePiLpTypedWeightedRowKernel

/-!
# Weighted rows of the generated CMP99 covariance transition

The complete generated transition acts between the literal consecutive source
regions.  Its pointwise decay and the source `tilde Pi^5` carrier bound give a
fixed weighted-row estimate with no ambient-volume factor.
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

/-- Explicit weighted-row amplitude obtained by spending half of the chosen
pointwise decay rate and summing over at most `20736` target sites. -/
noncomputable def cmp99SourceGeneratedPhysicalCoarseCovarianceTransitionWeightedRowAmplitude
    (M depth : ℕ) (spacing epsilon rate : ℝ) : ℝ :=
  cmp99SourceGeneratedPhysicalCoarseCovarianceTransitionNormBound
      4 M depth spacing epsilon *
    Real.exp ((2 * rate) * ((1 + 2 * 5 : ℕ) : ℝ)) * 20736

namespace CMP99SourceDependentOmegaGeometry

set_option maxRecDepth 3000
set_option maxHeartbeats 1500000

/-- The literal generated covariance transition has a source-fixed
weighted-row bound at every positive rate.  All geometric summation is paid
by the exact `tilde Pi^5` carrier budget. -/
theorem generatedPhysicalCoarseCovarianceTransitionCoordinates_weightedRowKernelBound
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
      (ι := ActiveGaugeRegion.Site
        (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r)))
      (κ := ActiveGaugeRegion.Site
        (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r)))
      (g := SUNLieCoord Nc)
      (D.generatedPhysicalCoarseCovarianceTransitionCoordinates hpi5 r hM
        depth hspacing background budget fineSmall hsmall)
      (D.generatedPhysicalCoarseCovarianceTransitionDist hpi5 r)
      (cmp99SourceGeneratedPhysicalCoarseCovarianceTransitionWeightedRowAmplitude
        M depth spacing epsilon rate)
      rate := by
  let C := D.generatedPhysicalCoarseCovarianceTransitionCoordinates hpi5 r
    hM depth hspacing background budget fineSmall hsmall
  let sourceDist :=
    D.generatedPhysicalCoarseCovarianceTransitionDist hpi5 r
  have hpoint : FinitePiLpTypedExponentialKernelBound C sourceDist
      (cmp99SourceGeneratedPhysicalCoarseCovarianceTransitionNormBound
          4 M depth spacing epsilon *
        Real.exp ((2 * rate) * ((1 + 2 * 5 : ℕ) : ℝ)))
      (2 * rate) := by
    exact D.generatedPhysicalCoarseCovarianceTransitionCoordinates_exponential
      hpi5 r hM depth hspacing (by positivity) background budget fineSmall
        hsmall
  have hcard : Fintype.card (ActiveGaugeRegion.Site
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r))) ≤
      20736 :=
    D.operatorCoarseRegion_site_card_le_pi5 hpi5
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
    C sourceDist hrate.le (by norm_num : (0 : ℝ) ≤ 20736) hpoint hsum
  simpa [C, sourceDist,
    cmp99SourceGeneratedPhysicalCoarseCovarianceTransitionWeightedRowAmplitude]
    using hrow

end CMP99SourceDependentOmegaGeometry

end
end YangMills.RG
