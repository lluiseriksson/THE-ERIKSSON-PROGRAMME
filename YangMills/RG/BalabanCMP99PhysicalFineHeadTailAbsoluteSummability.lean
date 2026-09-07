/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99PhysicalFineHeadTailWordExpansion

/-!
# Absolute summability of physical CMP99 coarse words

The existing reconstruction theorem proves convergence of each fixed
Neumann layer as a vector-valued series.  Interchanging that series with
the radial FTC integral in CMP102 equation (80) requires the stronger
statement that the norms are summable.  This module derives that fact from
the literal defect-layer estimate and transports it quantitatively through
the real-linear physical reconstruction.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

set_option maxHeartbeats 2000000 in
/-- Complete complex coarse words of a fixed Neumann length are absolutely
summable before physical reconstruction. -/
theorem
    summable_norm_cmp99SourcePi4ComplexBackgroundMinimizerWordTerms_of_source
    {M Q Nc R Δ : ℕ}
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
    (neumannLength : ℕ) :
    Summable fun word : Fin neumannLength → ℕ =>
      ‖cmp99SourcePi4ComplexBackgroundMinimizerWordTerm
        (R := R) anchor K hc hmass hK
        baseCoarseCovariance sigma word‖ := by
  let defectLayer := fun layer : ℕ =>
    cmp99SourcePi4ComplexCoarseRelativeDefectLayer
      (R := R) anchor K hc hmass hK
      baseCoarseCovariance sigma layer
  let left :=
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
        (R := R) anchor K hc hmass hK sigma *
      cmp99SourcePi4ComplexBlockAdjointMatrix
        (M := M) (Q := Q) (Nc := Nc)
  let right :=
    cmp116PhysicalEndomorphismComplexMatrix baseCoarseCovariance
  let L := complexMatrixTwoSidedCLM left right
  have hnormLayers :
      Summable fun layer : ℕ => ‖defectLayer layer‖ :=
    summable_norm_cmp99SourcePi4ComplexCoarseRelativeDefectLayer_of_source
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert htri hrange hΔ hΔ1 sigma
      hradius hRweak hdiff hcap hsmall
  have hnegNorm :
      Summable fun layer : ℕ => ‖-defectLayer layer‖ := by
    simpa only [norm_neg] using hnormLayers
  have hwordNorm :
      Summable fun word : Fin neumannLength → ℕ =>
        ‖cmp99OrderedTupleProduct
          (fun layer => -defectLayer layer) word‖ :=
    summable_norm_cmp99OrderedTupleProduct
      (fun layer => -defectLayer layer) hnegNorm neumannLength
  apply
    (hwordNorm.mul_left (ContinuousLinearMap.opNorm L)).of_nonneg_of_le
      (fun _ => norm_nonneg _)
  intro word
  have hL :=
    L.le_opNorm
      (cmp99OrderedTupleProduct
        (fun layer => -defectLayer layer) word)
  change
    ‖left *
        cmp99OrderedTupleProduct
          (fun layer => -defectLayer layer) word *
        right‖ ≤
      ContinuousLinearMap.opNorm L *
        ‖cmp99OrderedTupleProduct
          (fun layer => -defectLayer layer) word‖ at hL
  simpa only [cmp99SourcePi4ComplexBackgroundMinimizerWordTerm,
    defectLayer, left, right, Matrix.mul_assoc] using hL

/-- Complete physical coarse words of a fixed Neumann length are absolutely
summable after reconstruction. -/
theorem
    summable_norm_cmp99SourcePi4PhysicalBackgroundMinimizerWordTerms_of_source
    {M Q Nc R Δ : ℕ}
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
    (neumannLength : ℕ) :
    Summable fun word : Fin neumannLength → ℕ =>
      ‖cmp99SourcePi4PhysicalBackgroundMinimizerWordTerm
        (R := R) anchor K hc hmass hK
        baseCoarseCovariance sigma word‖ := by
  apply summable_norm_cmp99PhysicalRectangularOfComplexMatrix
  exact
    summable_norm_cmp99SourcePi4ComplexBackgroundMinimizerWordTerms_of_source
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert htri hrange hΔ hΔ1 sigma
      hradius hRweak hdiff hcap hsmall neumannLength

end

end YangMills.RG
