/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedCoarseCovarianceTransitionCoordinates
import YangMills.RG.BalabanCMP99SourceOperatorCoarseRegionDiameter
import YangMills.RG.FinitePiLpTypedKernel

/-!
# Decay of the generated CMP99 coarse-covariance transition

The terminal-coordinate theorem realizes the literal rectangular transition
on the original pair of physical source regions.  Their common `tilde Pi^5`
envelope has diameter at most eleven.  The already proved uniform operator
norm therefore gives a source-specific exponential kernel estimate at every
positive rate, with no ambient-volume factor or caller-supplied dictionary.
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

set_option maxRecDepth 2000
set_option maxHeartbeats 1000000

/-- Literal cross-region distance between a target in the smaller region and
a source in its immediate predecessor. -/
def generatedPhysicalCoarseCovarianceTransitionDist
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 1))
    (target : ActiveGaugeRegion.Site
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r)))
    (source : ActiveGaugeRegion.Site
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r))) : ℕ :=
  finBoxDist target.1 source.1

/-- Both consecutive regions lie in the same literal `tilde Pi^5`, hence the
cross-region distance has the source-uniform diameter eleven. -/
theorem generatedPhysicalCoarseCovarianceTransitionDist_le_pi5
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 1))
    (target : ActiveGaugeRegion.Site
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r)))
    (source : ActiveGaugeRegion.Site
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r))) :
    D.generatedPhysicalCoarseCovarianceTransitionDist hpi5 r target source ≤
      1 + 2 * 5 := by
  have hidx : cmp99OmegaTransitionIndex r ≤
      cmp99OmegaTransitionNextIndex r := by
    change r.val ≤ r.val + 1
    omega
  have htargetMem : target.1 ∈
      (D.operatorCoarseRegion hpi5
        (cmp99OmegaTransitionIndex r)).sites := by
    exact D.fineRegion_subset_of_le hidx target.2
  let targetLarge : ActiveGaugeRegion.Site
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r)) :=
    ⟨target.1, htargetMem⟩
  exact D.operatorCoarseRegion_siteFinBoxDist_le_pi5 hpi5
    (cmp99OmegaTransitionIndex r) targetLarge source

/-- Source-specific exponential decay of the complete generated rectangular
coarse-covariance transition at every positive rate. -/
theorem generatedPhysicalCoarseCovarianceTransitionCoordinates_exponential
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
      (ι := ActiveGaugeRegion.Site
        (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r)))
      (κ := ActiveGaugeRegion.Site
        (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r)))
      (g := SUNLieCoord Nc)
      (D.generatedPhysicalCoarseCovarianceTransitionCoordinates hpi5 r hM
        depth hspacing background budget fineSmall hsmall)
      (D.generatedPhysicalCoarseCovarianceTransitionDist hpi5 r)
      (cmp99SourceGeneratedPhysicalCoarseCovarianceTransitionNormBound
          4 M depth spacing epsilon *
        Real.exp (rate * ((1 + 2 * 5 : ℕ) : ℝ))) rate := by
  let C := D.generatedPhysicalCoarseCovarianceTransitionCoordinates hpi5 r
    hM depth hspacing background budget fineSmall hsmall
  let sourceDist :=
    D.generatedPhysicalCoarseCovarianceTransitionDist hpi5 r
  have hrange : FinitePiLpTypedFiniteRange C sourceDist (1 + 2 * 5) := by
    intro source target v hfar
    dsimp [sourceDist] at hfar
    have hnear :=
      D.generatedPhysicalCoarseCovarianceTransitionDist_le_pi5 hpi5 r
        target source
    omega
  have hkernel : FinitePiLpTypedKernelBound C (fun _ _ =>
      cmp99SourceGeneratedPhysicalCoarseCovarianceTransitionNormBound
        4 M depth spacing epsilon) := by
    have hentry := finitePiLpTypedKernelBound_const_opNorm C
    have hnorm :=
      D.norm_generatedPhysicalCoarseCovarianceTransitionCoordinates_le hpi5 r
        hM depth hspacing background budget fineSmall hsmall
    intro source target v
    exact (hentry source target v).trans
      (mul_le_mul_of_nonneg_right hnorm (norm_nonneg v))
  change FinitePiLpTypedExponentialKernelBound C sourceDist _ rate
  apply finitePiLpTypedExponentialKernelBound_of_finiteRange
  · unfold cmp99SourceGeneratedPhysicalCoarseCovarianceTransitionNormBound
    positivity
  · exact hrate
  · exact hrange
  · exact hkernel

end CMP99SourceDependentOmegaGeometry

end
end YangMills.RG
