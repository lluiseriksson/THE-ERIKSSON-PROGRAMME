/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceDependentRegionalTower
import YangMills.RG.BalabanCMP99SourceGeneratedPhysicalCoarseCovariance
import YangMills.RG.BalabanCMP99SourceRegionTransition

/-!
# Typed transitions for the generated multiscale source precision

This file lifts the literal consecutive CMP99 domains through the complete
multiscale realization, constructs restriction and zero extension between
their genuinely different Dirichlet spaces, and proves the rectangular
second-resolvent identity for the generated physical Greens.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

universe v

variable {Q M Nc j : ℕ} [NeZero Q] [NeZero M] [NeZero Nc]
variable {cell : FinBox 4 Q}
variable {ScaleSite : Fin (j + 2) → Type v}
variable [∀ r, DecidableEq (ScaleSite r)]
variable {Scaled : CMP99SourceScaledStratification
  (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
variable {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
variable {gap : Fin (j + 1) → ℕ}

namespace CMP99SourceDependentOmegaGeometry

/-- Consecutive source domains remain nested after any number of complete
order-`M` lifts. -/
theorem operatorRegion_transition_subset
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 1)) (depth : ℕ) :
    (D.operatorRegion (M := M) hpi5
        (cmp99OmegaTransitionNextIndex r) depth).sites ⊆
      (D.operatorRegion (M := M) hpi5
        (cmp99OmegaTransitionIndex r) depth).sites := by
  apply cmp99IteratedLiftActiveRegion_sites_mono
  change D.fineRegion (cmp99OmegaTransitionNextIndex r) ⊆
    D.fineRegion (cmp99OmegaTransitionIndex r)
  exact D.fineRegion_subset_of_le (by
    change r.val ≤ r.val + 1
    omega)

/-- Restriction between the two generated fine Dirichlet spaces. -/
noncomputable def generatedTransitionRestriction
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 1)) (depth : ℕ) :
    ActiveGaugeZeroCochain
        (D.operatorRegion (M := M) hpi5
          (cmp99OmegaTransitionIndex r) depth) (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain
        (D.operatorRegion (M := M) hpi5
          (cmp99OmegaTransitionNextIndex r) depth) (SUNLieCoord Nc) :=
  (restrictZeroCLM
    (D.operatorRegion (M := M) hpi5
      (cmp99OmegaTransitionNextIndex r) depth)).comp
    (extendZeroZeroCLM
      (D.operatorRegion (M := M) hpi5
        (cmp99OmegaTransitionIndex r) depth))

/-- Zero extension in the reverse direction. -/
noncomputable def generatedTransitionExtension
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 1)) (depth : ℕ) :
    ActiveGaugeZeroCochain
        (D.operatorRegion (M := M) hpi5
          (cmp99OmegaTransitionNextIndex r) depth) (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain
        (D.operatorRegion (M := M) hpi5
          (cmp99OmegaTransitionIndex r) depth) (SUNLieCoord Nc) :=
  (restrictZeroCLM
    (D.operatorRegion (M := M) hpi5
      (cmp99OmegaTransitionIndex r) depth)).comp
    (extendZeroZeroCLM
      (D.operatorRegion (M := M) hpi5
        (cmp99OmegaTransitionNextIndex r) depth))

/-- Restriction after extension is the identity on the smaller generated
regional field space. -/
theorem generatedTransitionRestriction_comp_extension
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 1)) (depth : ℕ) :
    (D.generatedTransitionRestriction (M := M) (Nc := Nc) hpi5 r depth).comp
        (D.generatedTransitionExtension (M := M) (Nc := Nc) hpi5 r depth) =
      ContinuousLinearMap.id ℝ
        (ActiveGaugeZeroCochain
          (D.operatorRegion (M := M) hpi5
            (cmp99OmegaTransitionNextIndex r) depth) (SUNLieCoord Nc)) := by
  apply ContinuousLinearMap.ext
  intro phi
  ext x
  have hxSmall := x.2
  have hxLarge := D.operatorRegion_transition_subset hpi5 r depth hxSmall
  simp [generatedTransitionRestriction, generatedTransitionExtension,
    restrictZeroCLM, extendZeroZeroCLM, hxLarge]

/-- Literal mismatch of the generated regional Greens. -/
noncomputable def generatedPhysicalGreenTransition
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 1)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    ActiveGaugeZeroCochain
        (D.operatorRegion (M := M) hpi5
          (cmp99OmegaTransitionIndex r) (depth + 1)) (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain
        (D.operatorRegion (M := M) hpi5
          (cmp99OmegaTransitionNextIndex r) (depth + 1)) (SUNLieCoord Nc) :=
  by
    let Elarge := ActiveGaugeZeroCochain
      (D.operatorRegion (M := M) hpi5
        (cmp99OmegaTransitionIndex r) (depth + 1)) (SUNLieCoord Nc)
    let Esmall := ActiveGaugeZeroCochain
      (D.operatorRegion (M := M) hpi5
        (cmp99OmegaTransitionNextIndex r) (depth + 1)) (SUNLieCoord Nc)
    let Gsmall : Esmall →L[ℝ] Esmall := by
      change ActiveGaugeZeroCochain
          (cmp99IteratedLiftActiveRegion
            (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r))
            (depth + 1)) (SUNLieCoord Nc) →L[ℝ]
        ActiveGaugeZeroCochain
          (cmp99IteratedLiftActiveRegion
            (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r))
            (depth + 1)) (SUNLieCoord Nc)
      exact cmp99SourceGeneratedPhysicalGreen (by norm_num) hM
        (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r))
        depth hspacing background budget fineSmall hsmall
    let Glarge : Elarge →L[ℝ] Elarge := by
      change ActiveGaugeZeroCochain
          (cmp99IteratedLiftActiveRegion
            (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r))
            (depth + 1)) (SUNLieCoord Nc) →L[ℝ]
        ActiveGaugeZeroCochain
          (cmp99IteratedLiftActiveRegion
            (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r))
            (depth + 1)) (SUNLieCoord Nc)
      exact cmp99SourceGeneratedPhysicalGreen (by norm_num) hM
        (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r))
        depth hspacing background budget fineSmall hsmall
    let R : Elarge →L[ℝ] Esmall :=
      D.generatedTransitionRestriction (M := M) (Nc := Nc) hpi5 r
        (depth + 1)
    exact Gsmall.comp R - R.comp Glarge

/-- C2: exact rectangular second-resolvent identity for the literal
source-generated regional precisions. -/
theorem generatedPhysicalGreen_transition_resolvent
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 1)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    D.generatedPhysicalGreenTransition (M := M) hpi5 r hM depth hspacing
        background budget fineSmall hsmall =
      (cmp99SourceGeneratedPhysicalGreen (by norm_num) hM
        (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r))
        depth hspacing background budget fineSmall hsmall).comp
        ((cmp99TypedPrecisionDefect
          (cmp99SourceGeneratedPhysicalPrecision (by norm_num) hM
            (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r))
            depth spacing epsilon background budget fineSmall)
          (cmp99SourceGeneratedPhysicalPrecision (by norm_num) hM
            (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r))
            depth spacing epsilon background budget fineSmall)
          (D.generatedTransitionRestriction (M := M) (Nc := Nc) hpi5 r
            (depth + 1))).comp
          (cmp99SourceGeneratedPhysicalGreen (by norm_num) hM
            (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r))
            depth hspacing background budget fineSmall hsmall)) := by
  unfold generatedPhysicalGreenTransition
  exact typedGreen_transition_resolvent _ _ _ _ _
    (cmp99SourceGeneratedPhysicalPrecision_comp_green (by norm_num) hM
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r)) depth
      hspacing background budget fineSmall hsmall)
    (cmp99SourceGeneratedPhysicalGreen_comp_precision (by norm_num) hM
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r)) depth
      hspacing background budget fineSmall hsmall)

end CMP99SourceDependentOmegaGeometry

end

end YangMills.RG
