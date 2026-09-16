/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedSectionCCutFactorDecay
import YangMills.RG.DependentFinitePiLpWeightedRowWalk

/-!
# Generated scale-typed CMP99 Section C tower

The `j+1` literal cut factors act between genuinely different terminal
coordinate carriers.  This module composes them as a dependent-arrow walk
and preserves one fixed weighted-row decay rate through the complete ordered
product.  No carrier is embedded into an ambient endomorphism space.
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

/-- Literal terminal-coordinate site family of the generated source regions. -/
abbrev GeneratedSectionCCoarseSiteFamily
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) :=
  ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s)

/-- Cross-scale metric on all generated terminal coordinate carriers. -/
def generatedSectionCCoarseCrossDist
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r s : Fin (j + 2))
    (target : D.GeneratedSectionCCoarseSiteFamily hpi5 s)
    (source : D.GeneratedSectionCCoarseSiteFamily hpi5 r) : ℕ :=
  finBoxDist target.1 source.1

@[simp] theorem generatedSectionCCoarseCrossDist_self
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 2)) (x : D.GeneratedSectionCCoarseSiteFamily hpi5 r) :
    D.generatedSectionCCoarseCrossDist hpi5 r r x x = 0 :=
  finBoxDist_self _

theorem generatedSectionCCoarseCrossDist_triangle
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r s t : Fin (j + 2))
    (target : D.GeneratedSectionCCoarseSiteFamily hpi5 t)
    (middle : D.GeneratedSectionCCoarseSiteFamily hpi5 s)
    (source : D.GeneratedSectionCCoarseSiteFamily hpi5 r) :
    D.generatedSectionCCoarseCrossDist hpi5 r t target source ≤
      D.generatedSectionCCoarseCrossDist hpi5 s t target middle +
        D.generatedSectionCCoarseCrossDist hpi5 r s middle source :=
  finBoxDist_triangle _ _ _

/-- On consecutive indices the tower metric is literally the native generated
transition metric. -/
theorem generatedSectionCCoarseCrossDist_transition
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 1)) :
    D.generatedSectionCCoarseCrossDist hpi5 r.castSucc r.succ =
      D.generatedPhysicalCoarseCovarianceTransitionDist hpi5 r :=
  rfl

/-- The `r`-th literal generated cut factor as one dependent arrow. -/
noncomputable def generatedSectionCCutTowerStep
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (Cuts : ∀ r : Fin (j + 1), D.GeneratedSectionCTransitionCutData hpi5 r)
    (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    (r : Fin (j + 1)) :
    DependentFinitePiLpArrow (D.GeneratedSectionCCoarseSiteFamily hpi5)
      (SUNLieCoord Nc) r.castSucc r.succ :=
  D.generatedPhysicalCoarseSectionCCutFactorCoordinates hpi5 r (Cuts r) hM
    depth hspacing background budget fineSmall hsmall

/-- Full ordered generated Section C path through all `j+1` transitions. -/
noncomputable def generatedSectionCCutFactorTower
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (Cuts : ∀ r : Fin (j + 1), D.GeneratedSectionCTransitionCutData hpi5 r)
    (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :=
  DependentArrowWalk.finSuccPath
    (D.generatedSectionCCutTowerStep hpi5 Cuts hM depth hspacing background
      budget fineSmall hsmall)

@[simp] theorem generatedSectionCCutFactorTower_length
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (Cuts : ∀ r : Fin (j + 1), D.GeneratedSectionCTransitionCutData hpi5 r)
    (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    (D.generatedSectionCCutFactorTower hpi5 Cuts hM depth hspacing background
      budget fineSmall hsmall).length = j + 1 := by
  simp [generatedSectionCCutFactorTower]

/-- The complete generated cut tower preserves one fixed weighted-row rate
and has the product of the explicit one-step amplitudes. -/
theorem generatedSectionCCutFactorTower_weightedRowKernelBound
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (Cuts : ∀ r : Fin (j + 1), D.GeneratedSectionCTransitionCutData hpi5 r)
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
    let walk := D.generatedSectionCCutFactorTower hpi5 Cuts hM depth hspacing
      background budget fineSmall hsmall
    FinitePiLpTypedWeightedRowKernelBound
      (dependentFinitePiLpWalkOperator
        (D.GeneratedSectionCCoarseSiteFamily hpi5) (SUNLieCoord Nc) walk)
      (D.generatedSectionCCoarseCrossDist hpi5
        (cmp99OmegaZeroIndex j) (cmp99OmegaLastIndex j))
      ((cmp99SourceGeneratedPhysicalCoarseRightFactorWeightedRowAmplitude
        M depth spacing epsilon rate) ^ (j + 1)) rate := by
  dsimp only
  let Site := D.GeneratedSectionCCoarseSiteFamily hpi5
  let crossDist := D.generatedSectionCCoarseCrossDist hpi5
  let step := D.generatedSectionCCutTowerStep hpi5 Cuts hM depth hspacing
    background budget fineSmall hsmall
  let A := cmp99SourceGeneratedPhysicalCoarseRightFactorWeightedRowAmplitude
    M depth spacing epsilon rate
  have hstep : ∀ r,
      FinitePiLpTypedWeightedRowKernelBound
        (step r) (crossDist r.castSucc r.succ) A rate := by
    intro r
    simpa [step, crossDist, A,
      generatedSectionCCoarseCrossDist_transition] using
      D.generatedPhysicalCoarseSectionCCutFactorCoordinates_weightedRowKernelBound
        hpi5 r (Cuts r) hM depth hspacing hrate background budget fineSmall
        hsmall
  have hfull :=
    dependentFinitePiLpWalkOperator_finSuccPath_weightedRowKernelBound
      Site (SUNLieCoord Nc) crossDist
      (fun r x => D.generatedSectionCCoarseCrossDist_self hpi5 r x)
      (fun r s t target middle source =>
        D.generatedSectionCCoarseCrossDist_triangle hpi5 r s t target middle
          source)
      step (fun _ => A) hrate.le hstep
  simpa [Site, crossDist, step, A, generatedSectionCCutFactorTower,
    cmp99OmegaZeroIndex, cmp99OmegaLastIndex] using hfull

end CMP99SourceDependentOmegaGeometry

end
end YangMills.RG
