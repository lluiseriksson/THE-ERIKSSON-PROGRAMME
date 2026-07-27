/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99ComplexCoarseFineWalkWordExpansion

/-!
# Literal fine head and tail expansion of complex CMP99 minimizer words

The coarse defect factors have already been refined into dependent choices
of physical fine walks.  This module also refines the complete covariance
at the head of a fixed minimizer word.  The resulting term has one literal
head walk, one literal fine walk below every coarse layer, and an exact
active carrier given by their union.
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

/-- Union of all literal fine-walk carriers selected below a coarse word. -/
noncomputable def cmp99SourcePi4CoarseFineWalkChoiceActive
    {M Q R n : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    {layerWord : Fin n → ℕ}
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord) :
    Finset (FinBox 4 (2 * Q)) :=
  Finset.univ.biUnion fun i =>
    cmp99SourcePi4FineWalkIndex.active anchor (choice i)

theorem mem_cmp99SourcePi4CoarseFineWalkChoiceActive_iff
    {M Q R n : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    {layerWord : Fin n → ℕ}
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (d : FinBox 4 (2 * Q)) :
    d ∈ cmp99SourcePi4CoarseFineWalkChoiceActive anchor choice ↔
      ∃ i : Fin n,
        d ∈ cmp99SourcePi4FineWalkIndex.active anchor (choice i) := by
  simp [cmp99SourcePi4CoarseFineWalkChoiceActive]

/-- Exact active carrier of a literal head walk followed by a dependent
choice of literal tail walks. -/
noncomputable def cmp99SourcePi4FineHeadTailActive
    {M Q R headLength n : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (head : CMP99SourcePi4FineWalkIndex M Q R headLength)
    {layerWord : Fin n → ℕ}
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord) :
    Finset (FinBox 4 (2 * Q)) :=
  cmp99SourcePi4FineWalkIndex.active anchor head ∪
    cmp99SourcePi4CoarseFineWalkChoiceActive anchor choice

theorem mem_cmp99SourcePi4FineHeadTailActive_iff
    {M Q R headLength n : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (head : CMP99SourcePi4FineWalkIndex M Q R headLength)
    {layerWord : Fin n → ℕ}
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (d : FinBox 4 (2 * Q)) :
    d ∈ cmp99SourcePi4FineHeadTailActive anchor head choice ↔
      d ∈ cmp99SourcePi4FineWalkIndex.active anchor head ∨
        ∃ i : Fin n,
          d ∈ cmp99SourcePi4FineWalkIndex.active anchor (choice i) := by
  simp [cmp99SourcePi4FineHeadTailActive,
    mem_cmp99SourcePi4CoarseFineWalkChoiceActive_iff]

/-- A complete minimizer word after refining its coarse factors, but before
refining its full covariance head. -/
noncomputable def cmp99SourcePi4ComplexBackgroundMinimizerChoiceWordTerm
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
    Matrix (FineCoord M Q Nc) (CoarseCoord Q Nc) ℂ :=
  (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
        (R := R) anchor K hc hmass hK sigma *
      cmp99SourcePi4ComplexBlockAdjointMatrix
        (M := M) (Q := Q) (Nc := Nc)) *
    cmp99SourcePi4ComplexCoarseFineWalkWordTerm
      anchor K hc hmass hK baseCoarseCovariance sigma layerWord choice *
    cmp116PhysicalEndomorphismComplexMatrix baseCoarseCovariance

/-- One completely literal term: a physical fine head walk, one physical
fine walk under every coarse layer, and the full-coupling coarse inverse. -/
noncomputable def cmp99SourcePi4ComplexFineHeadTailWordTerm
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
    Matrix (FineCoord M Q Nc) (CoarseCoord Q Nc) ℂ :=
  (cmp99SourcePi4ComplexFineWalkTerm
        anchor K hc hmass hK sigma head *
      cmp99SourcePi4ComplexBlockAdjointMatrix
        (M := M) (Q := Q) (Nc := Nc)) *
    cmp99SourcePi4ComplexCoarseFineWalkWordTerm
      anchor K hc hmass hK baseCoarseCovariance sigma layerWord choice *
    cmp116PhysicalEndomorphismComplexMatrix baseCoarseCovariance

/-- Refining the coarse factors of one minimizer word is a finite exact
sum.  No infinite series is rearranged here. -/
theorem
    cmp99SourcePi4ComplexBackgroundMinimizerWordTerm_eq_sum_fineWalkChoices
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
    cmp99SourcePi4ComplexBackgroundMinimizerWordTerm
        (R := R) anchor K hc hmass hK
        baseCoarseCovariance sigma layerWord =
      ∑ choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord,
        cmp99SourcePi4ComplexBackgroundMinimizerChoiceWordTerm
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice := by
  rw [cmp99SourcePi4ComplexBackgroundMinimizerWordTerm,
    cmp99OrderedCoarseRelativeDefectWord_eq_sum_fineWalkChoices]
  rw [Matrix.mul_sum]
  simpa [cmp99SourcePi4ComplexBackgroundMinimizerChoiceWordTerm] using
    (Matrix.sum_mul Finset.univ
      (fun choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord =>
        (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
              (R := R) anchor K hc hmass hK sigma *
            cmp99SourcePi4ComplexBlockAdjointMatrix
              (M := M) (Q := Q) (Nc := Nc)) *
          cmp99SourcePi4ComplexCoarseFineWalkWordTerm
            anchor K hc hmass hK baseCoarseCovariance
            sigma layerWord choice)
      (cmp116PhysicalEndomorphismComplexMatrix baseCoarseCovariance))

/-- Under the physical contour hypotheses, the literal pointwise complete
covariance is also the matrix `tsum` of its finite length layers. -/
theorem
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_eq_tsum_layers_of_source
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
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
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1) :
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
        (R := R) anchor K hc hmass hK sigma =
      ∑' headLength : ℕ,
        cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK sigma headLength := by
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
  funext row col
  rw [cmp116SourcePi4FullComplexWeakenedCovarianceMatrix]
  symm
  calc
    (∑' headLength : ℕ, sigmaLayer headLength) row col =
        (∑' headLength : ℕ, sigmaLayer headLength row) col := by
      exact congrFun (tsum_apply (x := row) hsigmaLayers) col
    _ = ∑' headLength : ℕ, sigmaLayer headLength row col :=
      tsum_apply ((Pi.summable.mp hsigmaLayers) row)

/-- One coarse-choice minimizer word is the length-ordered sum over a
literal physical head walk.  The finite head sum remains inside the length
`tsum`, so no exchange of infinite sums is used. -/
theorem
    cmp99SourcePi4ComplexBackgroundMinimizerChoiceWordTerm_eq_tsum_headWalks_of_source
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
    cmp99SourcePi4ComplexBackgroundMinimizerChoiceWordTerm
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice =
      ∑' headLength : ℕ,
        ∑ head : CMP99SourcePi4FineWalkIndex M Q R headLength,
          cmp99SourcePi4ComplexFineHeadTailWordTerm
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
  have hmatrix :
      cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
          (R := R) anchor K hc hmass hK sigma =
        ∑' headLength : ℕ, sigmaLayer headLength :=
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_eq_tsum_layers_of_source
      anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
      hΔ hΔ1 sigma hradius hRweak hdiff hcap hsmall
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
  calc
    cmp99SourcePi4ComplexBackgroundMinimizerChoiceWordTerm
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice =
      L (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
        (R := R) anchor K hc hmass hK sigma) := by
          simp [cmp99SourcePi4ComplexBackgroundMinimizerChoiceWordTerm,
            L, right, tail, complexMatrixTwoSidedCLM_apply,
            Matrix.mul_assoc]
    _ = L (∑' headLength : ℕ, sigmaLayer headLength) := by
      rw [hmatrix]
    _ = ∑' headLength : ℕ, L (sigmaLayer headLength) :=
      L.map_tsum hsigmaLayers
    _ = ∑' headLength : ℕ,
        L (∑ head : CMP99SourcePi4FineWalkIndex M Q R headLength,
          cmp99SourcePi4ComplexFineWalkTerm
            anchor K hc hmass hK sigma head) := by
      apply tsum_congr
      intro headLength
      apply congrArg L
      dsimp [sigmaLayer]
      exact
        cmp116SourcePi4FullComplexWeakenedCovarianceLayer_eq_sum_fineWalkTerms
          anchor K hc hmass hK sigma headLength
    _ = ∑' headLength : ℕ,
        ∑ head : CMP99SourcePi4FineWalkIndex M Q R headLength,
          cmp99SourcePi4ComplexFineHeadTailWordTerm
            anchor K hc hmass hK baseCoarseCovariance
            sigma head layerWord choice := by
      apply tsum_congr
      intro headLength
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro head _hhead
      simp [cmp99SourcePi4ComplexFineHeadTailWordTerm,
        L, right, tail, complexMatrixTwoSidedCLM_apply,
        Matrix.mul_assoc]

end

end YangMills.RG
