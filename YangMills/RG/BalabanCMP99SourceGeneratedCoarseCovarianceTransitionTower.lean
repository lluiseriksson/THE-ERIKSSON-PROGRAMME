/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedCoarseCovarianceTransitionWeightedRow
import YangMills.RG.DependentFinitePiLpWeightedRowWalk

/-!
# Ordered tower of generated CMP99 covariance transitions

The `j+1` literal consecutive covariance transitions act between genuinely
different regional carriers.  This module composes them as a dependent walk
and preserves one fixed weighted-row rate across the complete source order.
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
variable {sourceDist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
variable {gap : Fin (j + 1) → ℕ}

namespace CMP99SourceDependentOmegaGeometry

set_option maxRecDepth 3000
set_option maxHeartbeats 2000000

/-- Physical terminal-coordinate carrier at each member of the dependent
regional sequence. -/
abbrev GeneratedCoarseCovarianceSiteFamily
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) sourceDist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 2)) :=
  ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 r)

/-- One literal cross-region distance family for every pair of generated
regional carriers. -/
def generatedCoarseCovarianceCrossDist
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) sourceDist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r s : Fin (j + 2))
    (target : D.GeneratedCoarseCovarianceSiteFamily hpi5 s)
    (source : D.GeneratedCoarseCovarianceSiteFamily hpi5 r) : ℕ :=
  finBoxDist target.1 source.1

@[simp] theorem generatedCoarseCovarianceCrossDist_self
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) sourceDist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 2))
    (x : D.GeneratedCoarseCovarianceSiteFamily hpi5 r) :
    D.generatedCoarseCovarianceCrossDist hpi5 r r x x = 0 :=
  finBoxDist_self _

theorem generatedCoarseCovarianceCrossDist_triangle
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) sourceDist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r s t : Fin (j + 2))
    (target : D.GeneratedCoarseCovarianceSiteFamily hpi5 t)
    (middle : D.GeneratedCoarseCovarianceSiteFamily hpi5 s)
    (source : D.GeneratedCoarseCovarianceSiteFamily hpi5 r) :
    D.generatedCoarseCovarianceCrossDist hpi5 r t target source ≤
      D.generatedCoarseCovarianceCrossDist hpi5 s t target middle +
        D.generatedCoarseCovarianceCrossDist hpi5 r s middle source :=
  finBoxDist_triangle _ _ _

/-- At consecutive indices the global distance is definitionally the native
distance of the generated transition. -/
theorem generatedCoarseCovarianceCrossDist_transition
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) sourceDist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 1)) :
    D.generatedCoarseCovarianceCrossDist hpi5 r.castSucc r.succ =
      D.generatedPhysicalCoarseCovarianceTransitionDist hpi5 r := rfl

/-- The `r`-th generated covariance transition as one dependent arrow. -/
noncomputable def generatedCoarseCovarianceTransitionTowerStep
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) sourceDist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
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
    (r : Fin (j + 1)) :
    DependentFinitePiLpArrow
      (D.GeneratedCoarseCovarianceSiteFamily hpi5)
      (SUNLieCoord Nc) r.castSucc r.succ :=
  D.generatedPhysicalCoarseCovarianceTransitionCoordinates hpi5 r hM depth
    hspacing background budget fineSmall hsmall

/-- Complete source-ordered product of all `j+1` generated transitions. -/
noncomputable def generatedCoarseCovarianceTransitionTower
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) sourceDist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :=
  DependentArrowWalk.finSuccPath
    (D.generatedCoarseCovarianceTransitionTowerStep hpi5 hM depth hspacing
      background budget fineSmall hsmall)

@[simp] theorem generatedCoarseCovarianceTransitionTower_length
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) sourceDist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
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
    (D.generatedCoarseCovarianceTransitionTower hpi5 hM depth hspacing
      background budget fineSmall hsmall).length = j + 1 := by
  simp [generatedCoarseCovarianceTransitionTower]

/-- The complete generated transition tower preserves one chosen weighted-row
rate; only the explicit one-step amplitudes multiply. -/
theorem generatedCoarseCovarianceTransitionTower_weightedRowKernelBound
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) sourceDist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon rate : ℝ}
    (hspacing : 0 < spacing) (hrate : 0 < rate)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    let walk := D.generatedCoarseCovarianceTransitionTower hpi5 hM depth
      hspacing background budget fineSmall hsmall
    FinitePiLpTypedWeightedRowKernelBound
      (dependentFinitePiLpWalkOperator
        (D.GeneratedCoarseCovarianceSiteFamily hpi5) (SUNLieCoord Nc) walk)
      (D.generatedCoarseCovarianceCrossDist hpi5
        (cmp99OmegaZeroIndex j) (cmp99OmegaLastIndex j))
      ((cmp99SourceGeneratedPhysicalCoarseCovarianceTransitionWeightedRowAmplitude
        M depth spacing epsilon rate) ^ (j + 1)) rate := by
  dsimp only
  let Site := D.GeneratedCoarseCovarianceSiteFamily hpi5
  let crossDist := D.generatedCoarseCovarianceCrossDist hpi5
  let step := D.generatedCoarseCovarianceTransitionTowerStep hpi5 hM depth
    hspacing background budget fineSmall hsmall
  let A :=
    cmp99SourceGeneratedPhysicalCoarseCovarianceTransitionWeightedRowAmplitude
      M depth spacing epsilon rate
  have hstep : ∀ r, FinitePiLpTypedWeightedRowKernelBound
      (step r) (crossDist r.castSucc r.succ) A rate := by
    intro r
    simpa [step, crossDist, A,
      generatedCoarseCovarianceCrossDist_transition] using
      D.generatedPhysicalCoarseCovarianceTransitionCoordinates_weightedRowKernelBound
        hpi5 r hM depth hspacing hrate background budget fineSmall hsmall
  have hfull :=
    dependentFinitePiLpWalkOperator_finSuccPath_weightedRowKernelBound
      Site (SUNLieCoord Nc) crossDist
      (fun r x => D.generatedCoarseCovarianceCrossDist_self hpi5 r x)
      (fun r s t target middle source =>
        D.generatedCoarseCovarianceCrossDist_triangle hpi5 r s t target
          middle source)
      step (fun _ => A) hrate.le hstep
  simpa [Site, crossDist, step, A,
    generatedCoarseCovarianceTransitionTower,
    cmp99OmegaZeroIndex, cmp99OmegaLastIndex] using hfull

end CMP99SourceDependentOmegaGeometry

end
end YangMills.RG
