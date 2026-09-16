/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourcePartitionCutoffs
import YangMills.RG.BalabanCMP99SourceGeneratedMassRange

/-!
# The generated CMP99 Section C commutator factor

Printed CMP99 p. 412 lists, before the non-exhaustive word "etc.", the
factor

`tildeChi Q' [G'_{Pi0}, (h'_{Pi0})^2] G'_{Pi0} Q'^* h_Pi C_Pi h_Pi`.

This file reconstructs that factor on the literal generated regional tower.
The fine cutoff is not supplied as a function: it is the source square
partition evaluated at the terminal owner of the fine site.  The complete
factor is an endomorphism of one coarse regional carrier, in contrast to the
rectangular consecutive-region factor (3.97).
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

/-- A typed Section C endomorphism together with its proved operator-norm
budget.  This transparent record keeps downstream kernel arguments from
renormalizing the source-generated operator term. -/
structure CMP99SectionCTypedEndomorphismWithNorm
    (ι g : Type*) [Fintype ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (A : ℝ) where
  operator : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g
  norm_le : ‖operator‖ ≤ A

/-- Pull the literal source square partition back to the finest lattice by
the terminal-owner map of the generated `Q'` tower. -/
def cmp99SourceGeneratedFinePartitionCutoff
    (P : CMP99SourceSquarePartition Q) (cell : FinBox 4 Q)
    (Omega : ActiveGaugeRegion 4 (2 * Q)) (depth : ℕ)
    (x : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))) : ℝ :=
  P.value cell
    (cmp99GeneratedTerminalBlockSite M (2 * Q) (depth + 1) x.1)

theorem norm_cmp99SourceGeneratedFinePartitionCutoff_le_one
    (P : CMP99SourceSquarePartition Q) (cell : FinBox 4 Q)
    (Omega : ActiveGaugeRegion 4 (2 * Q)) (depth : ℕ)
    (x : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))) :
    ‖cmp99SourceGeneratedFinePartitionCutoff (M := M) P cell Omega depth x‖ ≤
      1 :=
  P.norm_value_le_one cell _

namespace CMP99SourceDependentOmegaGeometry

set_option maxRecDepth 3000
set_option maxHeartbeats 6000000

/-- The source-printed middle commutator
`Q' [G', (h')²] G' Q'^*` on the generated tower over one region. -/
noncomputable def generatedPhysicalCoarseSectionCCommutatorMiddle
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP99SourceSquarePartition Q)
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
      spacing epsilon < 1) := by
  let Omega := D.operatorCoarseRegion hpi5 s
  let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M)
    Omega (depth + 1)
  let T := regions.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
    (matrixSUNAdjointModel Nc) spacing epsilon background
    budget.toRadiusChain fineSmall
  let G := cmp99SourceGeneratedPhysicalGreen (show 2 ≤ 4 by norm_num) hM
    Omega depth hspacing background budget fineSmall hsmall
  let H := finitePiLpScalarMultiplier (g := SUNLieCoord Nc)
    (cmp99SourceGeneratedFinePartitionCutoff (M := M) P cell Omega depth)
  let H2 := H.comp H
  exact T.Qprime.comp ((G.comp H2 - H2.comp G).comp
    (G.comp T.weightedAdjoint))

/-- Transport the middle commutator to the literal coarse site coordinates
of the selected source region. -/
noncomputable def generatedPhysicalCoarseSectionCCommutatorMiddleCoordinates
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP99SourceSquarePartition Q)
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
        (D.operatorCoarseRegion hpi5 s)) (SUNLieCoord Nc) := by
  let F := D.generatedPhysicalCoarseSectionCCommutatorMiddle P hpi5 s hM
    depth hspacing background budget fineSmall hsmall
  let hs := cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
    (D.operatorCoarseRegion hpi5 s) (depth + 1) spacing epsilon background
    budget.toRadiusChain fineSmall
  exact cmp99SourceTerminalCLMTransport hs hs F

/-- Literal realization of the complete commutator species printed on CMP99
p. 412:
`tildeChi Q' [G', (h')²] G' Q'^* h_Pi C_Pi h_Pi`. -/
noncomputable def generatedPhysicalCoarseSectionCCommutatorFactorCoordinates
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP99SourceSquarePartition Q)
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
  let H := finitePiLpScalarMultiplier (g := SUNLieCoord Nc)
    (fun x : ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s) =>
      P.value cell x.1)
  let Exterior := finitePiLpScalarMultiplier (g := SUNLieCoord Nc)
    (fun x : ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s) =>
      cmp99SourcePiCharacteristic cell x.1)
  let Middle := D.generatedPhysicalCoarseSectionCCommutatorMiddleCoordinates
    P hpi5 s hM depth hspacing background budget fineSmall hsmall
  let C := D.generatedPhysicalCoarseCovarianceCoordinates hpi5 s hM depth
    hspacing background budget fineSmall hsmall
  Exterior.comp (Middle.comp (H.comp (C.comp H)))

/-- The generated commutator middle has the same explicit, volume-independent
budget as a coarse-middle transition defect. -/
theorem norm_generatedPhysicalCoarseSectionCCommutatorMiddle_le
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP99SourceSquarePartition Q)
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
    ‖D.generatedPhysicalCoarseSectionCCommutatorMiddle P hpi5 s hM depth
      hspacing background budget fineSmall hsmall‖ ≤
      cmp99SourceGeneratedPhysicalCoarseMiddleDefectNormBound
        M depth spacing epsilon := by
  let Omega := D.operatorCoarseRegion hpi5 s
  let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M)
    Omega (depth + 1)
  let T := regions.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
    (matrixSUNAdjointModel Nc) spacing epsilon background
    budget.toRadiusChain fineSmall
  let G := cmp99SourceGeneratedPhysicalGreen (show 2 ≤ 4 by norm_num) hM
    Omega depth hspacing background budget fineSmall hsmall
  let H := finitePiLpScalarMultiplier (g := SUNLieCoord Nc)
    (cmp99SourceGeneratedFinePartitionCutoff (M := M) P cell Omega depth)
  let H2 := H.comp H
  let c := cmp99SourceGeneratedCoercivity 4 M (depth + 1) spacing epsilon
  let W := cmp99SourceGeneratedWeightedAdjointNormBound M depth
  have hc : 0 < c :=
    cmp99SourceGeneratedCoercivity_pos 4 M depth hspacing hsmall
  have hQ : ‖T.Qprime‖ ≤ 1 :=
    regions.norm_weightedQprimeTower_Qprime_le_one
      (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc) hspacing
      background budget.toRadiusChain fineSmall
  have hW : ‖T.weightedAdjoint‖ ≤ W :=
    D.norm_generatedWeightedAdjoint_le hpi5 s hM depth hspacing background
      budget fineSmall
  have hG : ‖G‖ ≤ 1 / c := by
    simpa [G, c] using norm_covarianceOfIsCoerciveCLM_le
      (cmp99SourceGeneratedPhysicalPrecision (show 2 ≤ 4 by norm_num) hM
        Omega depth spacing epsilon background budget fineSmall)
      hc
      (isCoerciveCLM_cmp99SourceGeneratedPhysicalPrecision
        (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
        fineSmall hsmall)
  have hH : ‖H‖ ≤ 1 :=
    norm_finitePiLpScalarMultiplier_le_one _
      (norm_cmp99SourceGeneratedFinePartitionCutoff_le_one
        (M := M) P cell Omega depth)
  have hH2 : ‖H2‖ ≤ 1 := by
    calc
      ‖H2‖ ≤ ‖H‖ * ‖H‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hH hH (norm_nonneg H) zero_le_one
      _ = 1 := one_mul 1
  have hGH2 : ‖G.comp H2‖ ≤ 1 / c := by
    calc
      ‖G.comp H2‖ ≤ ‖G‖ * ‖H2‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (1 / c) * 1 :=
        mul_le_mul hG hH2 (norm_nonneg H2) (by positivity)
      _ = 1 / c := mul_one _
  have hH2G : ‖H2.comp G‖ ≤ 1 / c := by
    calc
      ‖H2.comp G‖ ≤ ‖H2‖ * ‖G‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (1 / c) :=
        mul_le_mul hH2 hG (norm_nonneg G) zero_le_one
      _ = 1 / c := one_mul _
  have hcomm : ‖G.comp H2 - H2.comp G‖ ≤ 2 * (1 / c) := by
    calc
      ‖G.comp H2 - H2.comp G‖ ≤ ‖G.comp H2‖ + ‖H2.comp G‖ :=
        norm_sub_le _ _
      _ ≤ (1 / c) + (1 / c) := add_le_add hGH2 hH2G
      _ = 2 * (1 / c) := by ring
  have hGW : ‖G.comp T.weightedAdjoint‖ ≤ (1 / c) * W := by
    calc
      ‖G.comp T.weightedAdjoint‖ ≤ ‖G‖ * ‖T.weightedAdjoint‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (1 / c) * W :=
        mul_le_mul hG hW (norm_nonneg T.weightedAdjoint) (by positivity)
  have hcommGW : ‖(G.comp H2 - H2.comp G).comp
      (G.comp T.weightedAdjoint)‖ ≤
      (2 * (1 / c)) * ((1 / c) * W) := by
    calc
      ‖(G.comp H2 - H2.comp G).comp (G.comp T.weightedAdjoint)‖ ≤
          ‖G.comp H2 - H2.comp G‖ * ‖G.comp T.weightedAdjoint‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (2 * (1 / c)) * ((1 / c) * W) :=
        mul_le_mul hcomm hGW (norm_nonneg _) (by positivity)
  unfold generatedPhysicalCoarseSectionCCommutatorMiddle
    cmp99SourceGeneratedPhysicalCoarseMiddleDefectNormBound
  change ‖T.Qprime.comp ((G.comp H2 - H2.comp G).comp
      (G.comp T.weightedAdjoint))‖ ≤ 2 * (1 / c) ^ 2 * W
  calc
    ‖T.Qprime.comp ((G.comp H2 - H2.comp G).comp
        (G.comp T.weightedAdjoint))‖ ≤
        ‖T.Qprime‖ * ‖(G.comp H2 - H2.comp G).comp
          (G.comp T.weightedAdjoint)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ((2 * (1 / c)) * ((1 / c) * W)) := by
      exact mul_le_mul hQ hcommGW (norm_nonneg _) zero_le_one
    _ = 2 * (1 / c) ^ 2 * W := by ring

/-- The exterior and partition cutoffs add no cost, and the covariance adds
exactly the already audited inverse-precision budget. -/
theorem norm_generatedPhysicalCoarseSectionCCommutatorFactorCoordinates_le
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP99SourceSquarePartition Q)
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
    ‖D.generatedPhysicalCoarseSectionCCommutatorFactorCoordinates P hpi5 s
      hM depth hspacing background budget fineSmall hsmall‖ ≤
      cmp99SourceGeneratedPhysicalCoarseRightFactorNormBound
        M depth spacing epsilon := by
  let H := finitePiLpScalarMultiplier (g := SUNLieCoord Nc)
    (fun x : ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s) =>
      P.value cell x.1)
  let Exterior := finitePiLpScalarMultiplier (g := SUNLieCoord Nc)
    (fun x : ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s) =>
      cmp99SourcePiCharacteristic cell x.1)
  let Middle := D.generatedPhysicalCoarseSectionCCommutatorMiddleCoordinates
    P hpi5 s hM depth hspacing background budget fineSmall hsmall
  let C := D.generatedPhysicalCoarseCovarianceCoordinates hpi5 s hM depth
    hspacing background budget fineSmall hsmall
  let AD := cmp99SourceGeneratedPhysicalCoarseMiddleDefectNormBound
    M depth spacing epsilon
  let AC := cmp99SourceGeneratedPhysicalCoarseCovarianceNormBound
    M depth spacing epsilon
  have hH : ‖H‖ ≤ 1 :=
    norm_finitePiLpScalarMultiplier_le_one _
      (fun x => P.norm_value_le_one cell x.1)
  have hE : ‖Exterior‖ ≤ 1 :=
    norm_finitePiLpScalarMultiplier_le_one _
      (fun x => norm_cmp99SourcePiCharacteristic_le_one cell x.1)
  have hMiddle : ‖Middle‖ ≤ AD := by
    let F := D.generatedPhysicalCoarseSectionCCommutatorMiddle P hpi5 s hM
      depth hspacing background budget fineSmall hsmall
    let hs := cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
      (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
      (D.operatorCoarseRegion hpi5 s) (depth + 1) spacing epsilon background
      budget.toRadiusChain fineSmall
    change ‖cmp99SourceTerminalCLMTransport hs hs F‖ ≤ AD
    rw [norm_cmp99SourceTerminalCLMTransport]
    exact D.norm_generatedPhysicalCoarseSectionCCommutatorMiddle_le P hpi5 s
      hM depth hspacing background budget fineSmall hsmall
  have hC : ‖C‖ ≤ AC :=
    D.norm_generatedPhysicalCoarseCovarianceCoordinates_le hpi5 s hM depth
      hspacing background budget fineSmall hsmall
  have hAD : 0 ≤ AD := by
    dsimp [AD, cmp99SourceGeneratedPhysicalCoarseMiddleDefectNormBound,
      cmp99SourceGeneratedWeightedAdjointNormBound]
    positivity
  have hAC : 0 ≤ AC := by
    dsimp [AC, cmp99SourceGeneratedPhysicalCoarseCovarianceNormBound]
    positivity
  have hCH : ‖C.comp H‖ ≤ AC * 1 := by
    calc
      ‖C.comp H‖ ≤ ‖C‖ * ‖H‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ AC * 1 := mul_le_mul hC hH (norm_nonneg H) hAC
  have hHCH : ‖H.comp (C.comp H)‖ ≤ 1 * (AC * 1) := by
    calc
      ‖H.comp (C.comp H)‖ ≤ ‖H‖ * ‖C.comp H‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (AC * 1) :=
        mul_le_mul hH hCH (norm_nonneg _) zero_le_one
  have hMHCH : ‖Middle.comp (H.comp (C.comp H))‖ ≤
      AD * (1 * (AC * 1)) := by
    calc
      ‖Middle.comp (H.comp (C.comp H))‖ ≤
          ‖Middle‖ * ‖H.comp (C.comp H)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ AD * (1 * (AC * 1)) :=
        mul_le_mul hMiddle hHCH (norm_nonneg _) hAD
  unfold generatedPhysicalCoarseSectionCCommutatorFactorCoordinates
  change ‖Exterior.comp (Middle.comp (H.comp (C.comp H)))‖ ≤ _
  calc
    ‖Exterior.comp (Middle.comp (H.comp (C.comp H)))‖ ≤
        ‖Exterior‖ * ‖Middle.comp (H.comp (C.comp H))‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (AD * (1 * (AC * 1))) := by
      exact mul_le_mul hE hMHCH (norm_nonneg _) zero_le_one
    _ = cmp99SourceGeneratedPhysicalCoarseRightFactorNormBound
        M depth spacing epsilon := by
      dsimp [AD, AC,
        cmp99SourceGeneratedPhysicalCoarseMiddleDefectNormBound,
        cmp99SourceGeneratedPhysicalCoarseCovarianceNormBound,
        cmp99SourceGeneratedPhysicalCoarseRightFactorNormBound]
      ring

/-- The exact printed commutator factor, packaged with the norm theorem just
proved.  No operator or estimate is supplied by the caller. -/
noncomputable def generatedPhysicalCoarseSectionCCommutatorFactorCertificate
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP99SourceSquarePartition Q)
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
      (cmp99SourceGeneratedPhysicalCoarseRightFactorNormBound
        M depth spacing epsilon) where
  operator := D.generatedPhysicalCoarseSectionCCommutatorFactorCoordinates P
    hpi5 s hM depth hspacing background budget fineSmall hsmall
  norm_le :=
    D.norm_generatedPhysicalCoarseSectionCCommutatorFactorCoordinates_le P
      hpi5 s hM depth hspacing background budget fineSmall hsmall

/-- The packaged operator is definitionally the literal p. 412 factor. -/
@[simp] theorem generatedPhysicalCoarseSectionCCommutatorFactorCertificate_operator
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP99SourceSquarePartition Q)
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
    (D.generatedPhysicalCoarseSectionCCommutatorFactorCertificate P hpi5 s
      hM depth hspacing background budget fineSmall hsmall).operator =
      D.generatedPhysicalCoarseSectionCCommutatorFactorCoordinates P hpi5 s
        hM depth hspacing background budget fineSmall hsmall := rfl

end CMP99SourceDependentOmegaGeometry

end
end YangMills.RG
