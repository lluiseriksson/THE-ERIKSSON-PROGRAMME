/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedSectionCCommutatorFactor
import YangMills.RG.BalabanCMP99SourceGeneratedSmoothGreenCommutator
import YangMills.RG.BalabanCMP95PeriodicSquarePartition

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

/-- Norm budget after attaching the two outer coarse cutoffs and the coarse
covariance appearing on the right of the printed p. 412 factor. -/
noncomputable def cmp99SourceGeneratedSmoothSectionCFactorNormBound
    (P : CMP95SourceSmoothPartitionProfile)
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  cmp99SourceGeneratedSmoothSectionCMiddleNormBound
      P M depth spacing epsilon *
    cmp99SourceGeneratedPhysicalCoarseCovarianceNormBound
      M depth spacing epsilon

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

/-- Complete source-printed p. 412 species with the smooth fine commutator:
`tildeChi Q' [G',(h')²] G' Q'^* h_Pi C_Pi h_Pi`. -/
noncomputable def generatedPhysicalSmoothSectionCCommutatorFactorCoordinates
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (fineProfile : CMP95SourceSmoothPartitionProfile)
    (coarsePartition : CMP99SourceSquarePartition Q)
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
        (D.operatorCoarseRegion hpi5 s)) (SUNLieCoord Nc) :=
  let H := finitePiLpScalarMultiplier (g := SUNLieCoord Nc)
    (fun x : ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s) =>
      coarsePartition.value cell x.1)
  let Exterior := finitePiLpScalarMultiplier (g := SUNLieCoord Nc)
    (fun x : ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s) =>
      cmp99SourcePiCharacteristic cell x.1)
  let Middle := D.generatedPhysicalSmoothSectionCCommutatorMiddleCoordinates
    fineProfile hpi5 s hM depth center hspacing background budget fineSmall
      hsmall
  let C := D.generatedPhysicalCoarseCovarianceCoordinates hpi5 s hM depth
    hspacing background budget fineSmall hsmall
  Exterior.comp (Middle.comp (H.comp (C.comp H)))

/-- The complete smooth commutator species retains the source `M0^-1`
commutator gain and has no ambient-volume cardinality in its norm budget. -/
theorem norm_generatedPhysicalSmoothSectionCCommutatorFactorCoordinates_le
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (fineProfile : CMP95SourceSmoothPartitionProfile)
    (coarsePartition : CMP99SourceSquarePartition Q)
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
    ‖D.generatedPhysicalSmoothSectionCCommutatorFactorCoordinates
      fineProfile coarsePartition hpi5 s hM depth center hspacing background
        budget fineSmall hsmall‖ ≤
      cmp99SourceGeneratedSmoothSectionCFactorNormBound
        fineProfile M depth spacing epsilon := by
  let H := finitePiLpScalarMultiplier (g := SUNLieCoord Nc)
    (fun x : ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s) =>
      coarsePartition.value cell x.1)
  let Exterior := finitePiLpScalarMultiplier (g := SUNLieCoord Nc)
    (fun x : ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s) =>
      cmp99SourcePiCharacteristic cell x.1)
  let Middle := D.generatedPhysicalSmoothSectionCCommutatorMiddleCoordinates
    fineProfile hpi5 s hM depth center hspacing background budget fineSmall
      hsmall
  let C := D.generatedPhysicalCoarseCovarianceCoordinates hpi5 s hM depth
    hspacing background budget fineSmall hsmall
  let AM := cmp99SourceGeneratedSmoothSectionCMiddleNormBound
    fineProfile M depth spacing epsilon
  let AC := cmp99SourceGeneratedPhysicalCoarseCovarianceNormBound
    M depth spacing epsilon
  have hH : ‖H‖ ≤ 1 :=
    norm_finitePiLpScalarMultiplier_le_one _
      (fun x => coarsePartition.norm_value_le_one cell x.1)
  have hE : ‖Exterior‖ ≤ 1 :=
    norm_finitePiLpScalarMultiplier_le_one _
      (fun x => norm_cmp99SourcePiCharacteristic_le_one cell x.1)
  have hMiddle : ‖Middle‖ ≤ AM :=
    D.norm_generatedPhysicalSmoothSectionCCommutatorMiddleCoordinates_le
      fineProfile hpi5 s hM depth center hspacing background budget fineSmall
        hsmall
  have hC : ‖C‖ ≤ AC :=
    D.norm_generatedPhysicalCoarseCovarianceCoordinates_le hpi5 s hM depth
      hspacing background budget fineSmall hsmall
  have hAM : 0 ≤ AM := (norm_nonneg Middle).trans hMiddle
  have hAC : 0 ≤ AC := (norm_nonneg C).trans hC
  have hCH : ‖C.comp H‖ ≤ AC := by
    calc
      ‖C.comp H‖ ≤ ‖C‖ * ‖H‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ AC * 1 := mul_le_mul hC hH (norm_nonneg H) hAC
      _ = AC := mul_one _
  have hHCH : ‖H.comp (C.comp H)‖ ≤ AC := by
    calc
      ‖H.comp (C.comp H)‖ ≤ ‖H‖ * ‖C.comp H‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * AC := mul_le_mul hH hCH (norm_nonneg _) zero_le_one
      _ = AC := one_mul _
  have hMHCH : ‖Middle.comp (H.comp (C.comp H))‖ ≤ AM * AC := by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hMiddle hHCH (norm_nonneg _) hAM)
  unfold generatedPhysicalSmoothSectionCCommutatorFactorCoordinates
  change ‖Exterior.comp (Middle.comp (H.comp (C.comp H)))‖ ≤ _
  calc
    ‖Exterior.comp (Middle.comp (H.comp (C.comp H)))‖ ≤
        ‖Exterior‖ * ‖Middle.comp (H.comp (C.comp H))‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (AM * AC) :=
      mul_le_mul hE hMHCH (norm_nonneg _) zero_le_one
    _ = cmp99SourceGeneratedSmoothSectionCFactorNormBound
        fineProfile M depth spacing epsilon := by
      simp only [one_mul]
      rfl

/-- The complete smooth p. 412 species packaged with its proved norm. -/
noncomputable def generatedPhysicalSmoothSectionCCommutatorFactorCertificate
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (fineProfile : CMP95SourceSmoothPartitionProfile)
    (coarsePartition : CMP99SourceSquarePartition Q)
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
    CMP99SectionCTypedEndomorphismWithNorm
      (ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s))
      (SUNLieCoord Nc)
      (cmp99SourceGeneratedSmoothSectionCFactorNormBound
        fineProfile M depth spacing epsilon) where
  operator := D.generatedPhysicalSmoothSectionCCommutatorFactorCoordinates
    fineProfile coarsePartition hpi5 s hM depth center hspacing background
      budget fineSmall hsmall
  norm_le :=
    D.norm_generatedPhysicalSmoothSectionCCommutatorFactorCoordinates_le
      fineProfile coarsePartition hpi5 s hM depth center hspacing background
        budget fineSmall hsmall

/-- The complete p. 412 smooth-commutator species with both cutoffs generated
from a single CMP95 (1.118) profile.  In particular, callers no longer supply
an abstract coarse square partition: its exact periodic normalization is
derived by residue-class regrouping. -/
noncomputable def generatedCMP95PhysicalSmoothSectionCCommutatorFactorCoordinates
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
        (D.operatorCoarseRegion hpi5 s)) (SUNLieCoord Nc) :=
  D.generatedPhysicalSmoothSectionCCommutatorFactorCoordinates P
    (cmp95SourcePeriodicCoarseSquarePartition P Q) hpi5 s hM depth center
      hspacing background budget fineSmall hsmall

/-- Source-profile-only norm theorem for the complete p. 412 species. -/
theorem norm_generatedCMP95PhysicalSmoothSectionCCommutatorFactorCoordinates_le
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
    ‖D.generatedCMP95PhysicalSmoothSectionCCommutatorFactorCoordinates P
      hpi5 s hM depth center hspacing background budget fineSmall hsmall‖ ≤
      cmp99SourceGeneratedSmoothSectionCFactorNormBound
        P M depth spacing epsilon := by
  exact D.norm_generatedPhysicalSmoothSectionCCommutatorFactorCoordinates_le
    P (cmp95SourcePeriodicCoarseSquarePartition P Q) hpi5 s hM depth center
      hspacing background budget fineSmall hsmall

/-- Fully generated certificate for the p. 412 species: one CMP95 profile
produces both the smooth commutator cutoff and the normalized coarse cutoff. -/
noncomputable def generatedCMP95PhysicalSmoothSectionCCommutatorFactorCertificate
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
    CMP99SectionCTypedEndomorphismWithNorm
      (ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s))
      (SUNLieCoord Nc)
      (cmp99SourceGeneratedSmoothSectionCFactorNormBound
        P M depth spacing epsilon) where
  operator := D.generatedCMP95PhysicalSmoothSectionCCommutatorFactorCoordinates
    P hpi5 s hM depth center hspacing background budget fineSmall hsmall
  norm_le :=
    D.norm_generatedCMP95PhysicalSmoothSectionCCommutatorFactorCoordinates_le
      P hpi5 s hM depth center hspacing background budget fineSmall hsmall

/-- Source-cell specialization of the complete smooth species.  The fine
cutoff centre is now the canonical generated representative of `cell`, so
neither a centre nor a coarse partition remains caller supplied. -/
noncomputable def generatedCMP95SourceCenteredSectionCCommutatorFactorCoordinates
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP95SourceSmoothPartitionProfile)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) (hM : 2 ≤ M) (depth : ℕ)
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
        (D.operatorCoarseRegion hpi5 s)) (SUNLieCoord Nc) :=
  D.generatedCMP95PhysicalSmoothSectionCCommutatorFactorCoordinates P hpi5 s
    hM depth (cmp99SourceGeneratedSmoothCutoffCenter M Q depth cell)
      hspacing background budget fineSmall hsmall

/-- Volume-independent norm estimate for the source-centred species. -/
theorem
    norm_generatedCMP95SourceCenteredSectionCCommutatorFactorCoordinates_le
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP95SourceSmoothPartitionProfile)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    ‖D.generatedCMP95SourceCenteredSectionCCommutatorFactorCoordinates P
      hpi5 s hM depth hspacing background budget fineSmall hsmall‖ ≤
      cmp99SourceGeneratedSmoothSectionCFactorNormBound
        P M depth spacing epsilon := by
  exact
    D.norm_generatedCMP95PhysicalSmoothSectionCCommutatorFactorCoordinates_le
      P hpi5 s hM depth
        (cmp99SourceGeneratedSmoothCutoffCenter M Q depth cell)
        hspacing background budget fineSmall hsmall

/-- Fully source-centred certificate for the complete printed species. -/
noncomputable def
    generatedCMP95SourceCenteredSectionCCommutatorFactorCertificate
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP95SourceSmoothPartitionProfile)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    CMP99SectionCTypedEndomorphismWithNorm
      (ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s))
      (SUNLieCoord Nc)
      (cmp99SourceGeneratedSmoothSectionCFactorNormBound
        P M depth spacing epsilon) where
  operator :=
    D.generatedCMP95SourceCenteredSectionCCommutatorFactorCoordinates P
      hpi5 s hM depth hspacing background budget fineSmall hsmall
  norm_le :=
    D.norm_generatedCMP95SourceCenteredSectionCCommutatorFactorCoordinates_le
      P hpi5 s hM depth hspacing background budget fineSmall hsmall

end CMP99SourceDependentOmegaGeometry

end

end YangMills.RG
