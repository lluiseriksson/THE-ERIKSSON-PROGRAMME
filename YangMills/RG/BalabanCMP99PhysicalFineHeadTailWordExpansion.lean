/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99ComplexFineHeadTailLocalization
import YangMills.RG.BalabanCMP99PhysicalRectangularMatrixReconstructionLinear

/-!
# Physical reconstruction of literal CMP99 head-tail walk terms

This module transports one complete, source-ordered head-walk expansion
from complex rectangular matrices to the real physical maps consumed by
CMP102 equation (80). The transport uses continuity and a proved
summability statement; no formal `tsum` is mapped without convergence.
-/

namespace YangMills.RG

noncomputable section

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

private abbrev FineCoord (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc

private abbrev CoarseCoord (Q Nc : ℕ)
    [NeZero Q] [NeZero (2 * Q)] :=
  CMP116PhysicalWalkCoordinate 4 (2 * Q) Nc

/-- Physical real reconstruction of one literal head-tail minimizer term. -/
noncomputable def cmp99SourcePi4PhysicalFineHeadTailWordTerm
    {M Q Nc R headLength n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (head : CMP99SourcePi4FineWalkIndex M Q R headLength)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord) :
    CoarseField Q Nc →L[ℝ] FineField M Q Nc :=
  cmp99PhysicalRectangularOfComplexMatrix
    (cmp99SourcePi4ComplexFineHeadTailWordTerm
      anchor K hc hmass hK baseCoarseCovariance
      sigma head layerWord choice)

/-- Physical real reconstruction of one coarse-choice minimizer word. -/
noncomputable def cmp99SourcePi4PhysicalBackgroundMinimizerChoiceWordTerm
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord) :
    CoarseField Q Nc →L[ℝ] FineField M Q Nc :=
  cmp99PhysicalRectangularOfComplexMatrix
    (cmp99SourcePi4ComplexBackgroundMinimizerChoiceWordTerm
      anchor K hc hmass hK baseCoarseCovariance
      sigma layerWord choice)

/-- Physical reconstruction of one complete coarse minimizer word before
choosing literal fine walks below its coarse layers. -/
noncomputable def cmp99SourcePi4PhysicalBackgroundMinimizerWordTerm
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (layerWord : Fin n → ℕ) :
    CoarseField Q Nc →L[ℝ] FineField M Q Nc :=
  cmp99PhysicalRectangularOfComplexMatrix
    (cmp99SourcePi4ComplexBackgroundMinimizerWordTerm
      (R := R) anchor K hc hmass hK baseCoarseCovariance
      sigma layerWord)

/-- Refinement of a physical coarse word into its dependent finite family
of literal tail choices is exact. -/
theorem
    cmp99SourcePi4PhysicalBackgroundMinimizerWordTerm_eq_sum_fineWalkChoices
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (layerWord : Fin n → ℕ) :
    cmp99SourcePi4PhysicalBackgroundMinimizerWordTerm
        (R := R) anchor K hc hmass hK
        baseCoarseCovariance sigma layerWord =
      ∑ choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord,
        cmp99SourcePi4PhysicalBackgroundMinimizerChoiceWordTerm
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice := by
  unfold cmp99SourcePi4PhysicalBackgroundMinimizerWordTerm
    cmp99SourcePi4PhysicalBackgroundMinimizerChoiceWordTerm
  rw [
    cmp99SourcePi4ComplexBackgroundMinimizerWordTerm_eq_sum_fineWalkChoices,
    cmp99PhysicalRectangularOfComplexMatrix_sum]

/-- One reconstructed physical coarse-choice word is the genuinely
summable, length-ordered series of reconstructed literal head walks. -/
theorem
    cmp99SourcePi4PhysicalBackgroundMinimizerChoiceWordTerm_eq_tsum_headWalks_of_source
    {M Q Nc R Δ n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    {Ahead rho rate radius Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hdiff : ∀ d, ‖sigma d - 1‖ ≤ radius)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord) :
    cmp99SourcePi4PhysicalBackgroundMinimizerChoiceWordTerm
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice =
      ∑' headLength : ℕ,
        ∑ head : CMP99SourcePi4FineWalkIndex M Q R headLength,
          cmp99SourcePi4PhysicalFineHeadTailWordTerm
            anchor K hc hmass hK baseCoarseCovariance
            sigma head layerWord choice := by
  let sigmaLayer := fun headLength : ℕ =>
    cmp116SourcePi4FullComplexWeakenedCovarianceLayer
      (R := R) anchor K hc hmass hK sigma headLength
  let oneLayer := fun headLength : ℕ =>
    cmp116SourcePi4FullComplexWeakenedCovarianceLayer
      (R := R) anchor K hc hmass hK (fun _ => 1) headLength
  have hdiffLayers : Summable fun headLength : ℕ =>
      sigmaLayer headLength - oneLayer headLength :=
    summable_cmp116SourcePi4FullComplexWeakenedCovarianceLayer_sub_one
      anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
      hΔ hΔ1 sigma hradius hRweak hdiff hcap hsmall
  have honeLayers : Summable oneLayer :=
    summable_cmp116SourcePi4FullComplexWeakenedCovarianceLayer_one
      anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
      hΔ hΔ1 hRweak hsmall
  have hsigmaLayers : Summable sigmaLayer := by
    exact (hdiffLayers.add honeLayers).congr fun headLength => by
      exact sub_add_cancel
        (sigmaLayer headLength) (oneLayer headLength)
  let tail :=
    cmp99SourcePi4ComplexCoarseFineWalkWordTerm
      anchor K hc hmass hK baseCoarseCovariance
      sigma layerWord choice
  let right :=
    cmp99SourcePi4ComplexBlockAdjointMatrix
        (M := M) (Q := Q) (Nc := Nc) *
      tail *
      cmp116PhysicalEndomorphismComplexMatrix baseCoarseCovariance
  let L :=
    complexMatrixTwoSidedCLM
      (1 : Matrix (FineCoord M Q Nc) (FineCoord M Q Nc) ℂ)
      right
  have hmatrix :
      ∀ headLength : ℕ,
        (∑ head : CMP99SourcePi4FineWalkIndex M Q R headLength,
          cmp99SourcePi4ComplexFineHeadTailWordTerm
            anchor K hc hmass hK baseCoarseCovariance
            sigma head layerWord choice) =
          L (sigmaLayer headLength) := by
    intro headLength
    symm
    dsimp [sigmaLayer]
    rw [
      cmp116SourcePi4FullComplexWeakenedCovarianceLayer_eq_sum_fineWalkTerms]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro head _hhead
    simp [cmp99SourcePi4ComplexFineHeadTailWordTerm,
      L, right, tail, complexMatrixTwoSidedCLM_apply,
      Matrix.mul_assoc]
  have hmatrixSummable :
      Summable fun headLength : ℕ =>
        ∑ head : CMP99SourcePi4FineWalkIndex M Q R headLength,
          cmp99SourcePi4ComplexFineHeadTailWordTerm
            anchor K hc hmass hK baseCoarseCovariance
            sigma head layerWord choice := by
    exact
      (hsigmaLayers.map L L.continuous).congr fun headLength =>
        (hmatrix headLength).symm
  unfold cmp99SourcePi4PhysicalBackgroundMinimizerChoiceWordTerm
  rw [
    cmp99SourcePi4ComplexBackgroundMinimizerChoiceWordTerm_eq_tsum_headWalks_of_source
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert htri hrange hΔ hΔ1
      sigma hradius hRweak hdiff hcap hsmall layerWord choice,
    cmp99PhysicalRectangularOfComplexMatrix_tsum _ hmatrixSummable]
  apply tsum_congr
  intro headLength
  rw [cmp99PhysicalRectangularOfComplexMatrix_sum]
  rfl

/-- The reconstructed length layers in the preceding physical expansion
are genuinely summable. This is exported separately so equation (80) can
map the series through its continuous direction functional. -/
theorem
    summable_cmp99SourcePi4PhysicalFineHeadTailWordTerms_of_source
    {M Q Nc R Δ n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    {Ahead rho rate radius Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hdiff : ∀ d, ‖sigma d - 1‖ ≤ radius)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord) :
    Summable fun headLength : ℕ =>
      ∑ head : CMP99SourcePi4FineWalkIndex M Q R headLength,
        cmp99SourcePi4PhysicalFineHeadTailWordTerm
          anchor K hc hmass hK baseCoarseCovariance
          sigma head layerWord choice := by
  let sigmaLayer := fun headLength : ℕ =>
    cmp116SourcePi4FullComplexWeakenedCovarianceLayer
      (R := R) anchor K hc hmass hK sigma headLength
  let oneLayer := fun headLength : ℕ =>
    cmp116SourcePi4FullComplexWeakenedCovarianceLayer
      (R := R) anchor K hc hmass hK (fun _ => 1) headLength
  have hdiffLayers : Summable fun headLength : ℕ =>
      sigmaLayer headLength - oneLayer headLength :=
    summable_cmp116SourcePi4FullComplexWeakenedCovarianceLayer_sub_one
      anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
      hΔ hΔ1 sigma hradius hRweak hdiff hcap hsmall
  have honeLayers : Summable oneLayer :=
    summable_cmp116SourcePi4FullComplexWeakenedCovarianceLayer_one
      anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
      hΔ hΔ1 hRweak hsmall
  have hsigmaLayers : Summable sigmaLayer := by
    exact (hdiffLayers.add honeLayers).congr fun headLength => by
      exact sub_add_cancel
        (sigmaLayer headLength) (oneLayer headLength)
  let tail :=
    cmp99SourcePi4ComplexCoarseFineWalkWordTerm
      anchor K hc hmass hK baseCoarseCovariance
      sigma layerWord choice
  let right :=
    cmp99SourcePi4ComplexBlockAdjointMatrix
        (M := M) (Q := Q) (Nc := Nc) *
      tail *
      cmp116PhysicalEndomorphismComplexMatrix baseCoarseCovariance
  let L :=
    complexMatrixTwoSidedCLM
      (1 : Matrix (FineCoord M Q Nc) (FineCoord M Q Nc) ℂ)
      right
  have hmatrix :
      ∀ headLength : ℕ,
        (∑ head : CMP99SourcePi4FineWalkIndex M Q R headLength,
          cmp99SourcePi4ComplexFineHeadTailWordTerm
            anchor K hc hmass hK baseCoarseCovariance
            sigma head layerWord choice) =
          L (sigmaLayer headLength) := by
    intro headLength
    symm
    dsimp [sigmaLayer]
    rw [
      cmp116SourcePi4FullComplexWeakenedCovarianceLayer_eq_sum_fineWalkTerms]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro head _hhead
    simp [cmp99SourcePi4ComplexFineHeadTailWordTerm,
      L, right, tail, complexMatrixTwoSidedCLM_apply,
      Matrix.mul_assoc]
  have hmatrixSummable :
      Summable fun headLength : ℕ =>
        ∑ head : CMP99SourcePi4FineWalkIndex M Q R headLength,
          cmp99SourcePi4ComplexFineHeadTailWordTerm
            anchor K hc hmass hK baseCoarseCovariance
            sigma head layerWord choice := by
    exact
      (hsigmaLayers.map L L.continuous).congr fun headLength =>
        (hmatrix headLength).symm
  have hreconstructed :=
    summable_cmp99PhysicalRectangularOfComplexMatrix
      (fun headLength : ℕ =>
        ∑ head : CMP99SourcePi4FineWalkIndex M Q R headLength,
          cmp99SourcePi4ComplexFineHeadTailWordTerm
            anchor K hc hmass hK baseCoarseCovariance
            sigma head layerWord choice)
      hmatrixSummable
  exact hreconstructed.congr fun headLength => by
    rw [cmp99PhysicalRectangularOfComplexMatrix_sum]
    rfl

/-- Reconstructed literal terms retain their exact source weakening
carrier. -/
theorem cmp99SourcePi4PhysicalFineHeadTailWordTerm_eq_of_eqOn_active
    {M Q Nc R headLength n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (sigma tau : FinBox 4 (2 * Q) → ℂ)
    (head : CMP99SourcePi4FineWalkIndex M Q R headLength)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (h : ∀ d ∈ cmp99SourcePi4FineHeadTailActive
      anchor head choice, sigma d = tau d) :
    cmp99SourcePi4PhysicalFineHeadTailWordTerm
        anchor K hc hmass hK baseCoarseCovariance
        sigma head layerWord choice =
      cmp99SourcePi4PhysicalFineHeadTailWordTerm
        anchor K hc hmass hK baseCoarseCovariance
        tau head layerWord choice := by
  unfold cmp99SourcePi4PhysicalFineHeadTailWordTerm
  rw [
    cmp99SourcePi4ComplexFineHeadTailWordTerm_eq_of_eqOn_active
      anchor K hc hmass hK baseCoarseCovariance
      sigma tau head layerWord choice h]

end

end YangMills.RG
