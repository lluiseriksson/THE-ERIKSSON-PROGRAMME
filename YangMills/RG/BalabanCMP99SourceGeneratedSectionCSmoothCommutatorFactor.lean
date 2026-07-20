/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedSectionCCommutatorFactor
import YangMills.RG.BalabanCMP99SourceGeneratedSmoothGreenCommutator

/-!
# The smooth CMP99 Section C commutator middle

CMP99 p. 412 contains the middle factor

`Q' [G'_{Pi0}, (h'_{Pi0})^2] G'_{Pi0} Q'^*`.

The older generated realization used the block-constant pullback of an
abstract square partition and could therefore prove only a contractive norm
bound.  This module inserts the smooth CMP95 (1.118) profile at its literal
generated scale `M^(depth+2)`.  Consequently the norm certificate retains the
cutoff derivative and the `M0^-1` factor produced before composition.

The periodic-distance representative below is an analytic realization of one
cutoff.  Identification of the complete translated family with the square
partition of (1.118) remains a separate source-dictionary theorem.
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

/-- Explicit norm budget inherited by the smooth commutator itself. -/
noncomputable def cmp99SourceGeneratedSmoothGreenCommutatorNormBound
    (P : CMP95SourceSmoothPartitionProfile)
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  ((4 * ((P.derivBound /
      cmp99SourceGeneratedSmoothCutoffScale M depth) * 4) *
        (2 / cmp99SourceGeneratedCoercivity
          4 M (depth + 1) spacing epsilon)) /
    cmp99SourceGeneratedCombesThomasRate 4 M depth spacing epsilon) *
  cmp99OmegaSiteExpSumBound
    (cmp99SourceGeneratedCombesThomasRate
      4 M depth spacing epsilon / 2)

/-- Explicit norm budget after attaching the right Green and weighted
adjoint, while the leading `Q'` remains contractive. -/
noncomputable def cmp99SourceGeneratedSmoothSectionCMiddleNormBound
    (P : CMP95SourceSmoothPartitionProfile)
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  cmp99SourceGeneratedSmoothGreenCommutatorNormBound
      P M depth spacing epsilon *
    ((1 / cmp99SourceGeneratedCoercivity
      4 M (depth + 1) spacing epsilon) *
      cmp99SourceGeneratedWeightedAdjointNormBound M depth)

namespace CMP99SourceDependentOmegaGeometry

set_option maxRecDepth 3000
set_option maxHeartbeats 6000000

/-- Literal smooth realization of the p. 412 middle factor on the generated
fine regional tower. -/
noncomputable def generatedPhysicalSmoothSectionCCommutatorMiddle
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP95SourceSmoothPartitionProfile)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) (hM : 2 ≤ M) (depth : ℕ)
    (center : FinBox 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)))
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) := by
  let Omega := D.operatorCoarseRegion hpi5 s
  let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M)
    Omega (depth + 1)
  let T := regions.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
    (matrixSUNAdjointModel Nc) spacing epsilon background
    budget.toRadiusChain fineSmall
  let G := cmp99SourceGeneratedPhysicalGreen (show 2 ≤ 4 by norm_num) hM
    Omega depth hspacing background budget fineSmall hsmall
  let K := cmp99SourceGeneratedPhysicalGreenSmoothSquareCommutator
    P Omega (fun _ => 0)
      (fun x => finTorusDistanceCoordinates center x.1)
      hM hspacing background budget fineSmall hsmall
  exact T.Qprime.comp (K.comp (G.comp T.weightedAdjoint))

/-- The smooth middle transported isometrically to the literal coarse site
coordinates of the selected source region. -/
noncomputable def generatedPhysicalSmoothSectionCCommutatorMiddleCoordinates
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP95SourceSmoothPartitionProfile)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) (hM : 2 ≤ M) (depth : ℕ)
    (center : FinBox 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)))
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    FinitePiLpField (ActiveGaugeRegion.Site
        (D.operatorCoarseRegion hpi5 s)) (SUNLieCoord Nc) →L[ℝ]
      FinitePiLpField (ActiveGaugeRegion.Site
        (D.operatorCoarseRegion hpi5 s)) (SUNLieCoord Nc) := by
  let F := D.generatedPhysicalSmoothSectionCCommutatorMiddle P hpi5 s hM
    depth center hspacing background budget fineSmall hsmall
  let hs := cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
    (D.operatorCoarseRegion hpi5 s) (depth + 1) spacing epsilon background
    budget.toRadiusChain fineSmall
  exact cmp99SourceTerminalCLMTransport hs hs F

/-- The smooth p. 412 middle has a volume-independent norm certificate whose
commutator factor contains the source derivative scale explicitly. -/
theorem norm_generatedPhysicalSmoothSectionCCommutatorMiddle_le
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP95SourceSmoothPartitionProfile)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) (hM : 2 ≤ M) (depth : ℕ)
    (center : FinBox 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)))
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    ‖D.generatedPhysicalSmoothSectionCCommutatorMiddle P hpi5 s hM depth
      center hspacing background budget fineSmall hsmall‖ ≤
      cmp99SourceGeneratedSmoothSectionCMiddleNormBound
        P M depth spacing epsilon := by
  let Omega := D.operatorCoarseRegion hpi5 s
  let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M)
    Omega (depth + 1)
  let T := regions.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
    (matrixSUNAdjointModel Nc) spacing epsilon background
    budget.toRadiusChain fineSmall
  let G := cmp99SourceGeneratedPhysicalGreen (show 2 ≤ 4 by norm_num) hM
    Omega depth hspacing background budget fineSmall hsmall
  let K := cmp99SourceGeneratedPhysicalGreenSmoothSquareCommutator
    P Omega (fun _ => 0)
      (fun x => finTorusDistanceCoordinates center x.1)
      hM hspacing background budget fineSmall hsmall
  let c := cmp99SourceGeneratedCoercivity 4 M (depth + 1) spacing epsilon
  let W := cmp99SourceGeneratedWeightedAdjointNormBound M depth
  let AK := cmp99SourceGeneratedSmoothGreenCommutatorNormBound
    P M depth spacing epsilon
  have hc : 0 < c :=
    cmp99SourceGeneratedCoercivity_pos 4 M depth hspacing hsmall
  have hQ : ‖T.Qprime‖ ≤ 1 :=
    regions.norm_weightedQprimeTower_Qprime_le_one
      (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc) hspacing
      background budget.toRadiusChain fineSmall
  have hK : ‖K‖ ≤ AK := by
    simpa [K, AK, cmp99SourceGeneratedSmoothGreenCommutatorNormBound] using
      norm_cmp99SourceGeneratedPhysicalGreenSmoothSquareCommutator_torusDistance_le
        P Omega center hM hspacing background budget fineSmall hsmall
  have hG : ‖G‖ ≤ 1 / c := by
    simpa [G, c] using norm_covarianceOfIsCoerciveCLM_le
      (cmp99SourceGeneratedPhysicalPrecision (show 2 ≤ 4 by norm_num) hM
        Omega depth spacing epsilon background budget fineSmall)
      hc
      (isCoerciveCLM_cmp99SourceGeneratedPhysicalPrecision
        (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
        fineSmall hsmall)
  have hW : ‖T.weightedAdjoint‖ ≤ W :=
    D.norm_generatedWeightedAdjoint_le hpi5 s hM depth hspacing background
      budget fineSmall
  have hAK : 0 ≤ AK := (norm_nonneg K).trans hK
  have hGW : ‖G.comp T.weightedAdjoint‖ ≤ (1 / c) * W := by
    calc
      ‖G.comp T.weightedAdjoint‖ ≤ ‖G‖ * ‖T.weightedAdjoint‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (1 / c) * W :=
        mul_le_mul hG hW (norm_nonneg _) (by positivity)
  unfold generatedPhysicalSmoothSectionCCommutatorMiddle
  change ‖T.Qprime.comp (K.comp (G.comp T.weightedAdjoint))‖ ≤ _
  calc
    ‖T.Qprime.comp (K.comp (G.comp T.weightedAdjoint))‖ ≤
        ‖T.Qprime‖ * ‖K.comp (G.comp T.weightedAdjoint)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (AK * ((1 / c) * W)) := by
      gcongr
      exact (ContinuousLinearMap.opNorm_comp_le K
        (G.comp T.weightedAdjoint)).trans
          (mul_le_mul hK hGW (norm_nonneg _) hAK)
    _ = cmp99SourceGeneratedSmoothSectionCMiddleNormBound
        P M depth spacing epsilon := by
      simp only [one_mul]
      rfl

/-- Isometric coarse-coordinate version of the smooth middle bound. -/
theorem norm_generatedPhysicalSmoothSectionCCommutatorMiddleCoordinates_le
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP95SourceSmoothPartitionProfile)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) (hM : 2 ≤ M) (depth : ℕ)
    (center : FinBox 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)))
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    ‖D.generatedPhysicalSmoothSectionCCommutatorMiddleCoordinates P hpi5 s
      hM depth center hspacing background budget fineSmall hsmall‖ ≤
      cmp99SourceGeneratedSmoothSectionCMiddleNormBound
        P M depth spacing epsilon := by
  let F := D.generatedPhysicalSmoothSectionCCommutatorMiddle P hpi5 s hM
    depth center hspacing background budget fineSmall hsmall
  let hs := cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
    (D.operatorCoarseRegion hpi5 s) (depth + 1) spacing epsilon background
    budget.toRadiusChain fineSmall
  change ‖cmp99SourceTerminalCLMTransport hs hs F‖ ≤ _
  rw [norm_cmp99SourceTerminalCLMTransport]
  exact D.norm_generatedPhysicalSmoothSectionCCommutatorMiddle_le P hpi5 s
    hM depth center hspacing background budget fineSmall hsmall

end CMP99SourceDependentOmegaGeometry

end

end YangMills.RG
