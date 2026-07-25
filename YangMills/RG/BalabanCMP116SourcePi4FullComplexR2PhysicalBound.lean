/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4FullComplexR2TransposePhysicalBound
import YangMills.RG.BalabanCMP116SourcePi4PhysicalComplexContourNonsingularity

/-!
# Physical bilateral bounds for the source-complex `R2`

This module supplies the row companion of the previously established column
bound.  Both orientations are now generated from the same physical contour
defect and their respective scalar Neumann conditions.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- Explicit source `R2` row budget. -/
noncomputable def cmp116SourcePi4PhysicalComplexR2RowBound
    {M Q Nc : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    (Delta : ℕ) (Ahead rho rate radius Rweak : ℝ) : ℝ :=
  let precisionRow := ‖cmp116PhysicalEndomorphismComplexMatrix K‖
  let covarianceDefect :=
    cmp116SourcePi4PhysicalComplexContourDefectBound
      Nc Delta Ahead rho rate radius Rweak
  let relativeDefect := precisionRow * covarianceDefect
  ((1 - relativeDefect)⁻¹ * precisionRow) *
    covarianceDefect * precisionRow

set_option maxHeartbeats 6000000 in
/-- The literal source-complex `R2` has a volume-uniform row bound produced
entirely from the physical contour certificate. -/
theorem linfty_opNorm_cmp116SourcePi4FullComplexR2Matrix_le_physical
    {M Q Nc R Delta : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hfiniteRange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          hc hmass hK‖ < 1)
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
    (hDelta : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Delta)
    (hDelta1 : 1 ≤ Delta)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hdiff : ∀ d, ‖sigma d - 1‖ ≤ radius)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (hseries :
      ‖cmp116SourcePi4ComplexContourRatio Delta rho Rweak‖ < 1)
    (hneumann :
      ‖cmp116PhysicalEndomorphismComplexMatrix K‖ *
        cmp116SourcePi4PhysicalComplexContourDefectBound
          Nc Delta Ahead rho rate radius Rweak < 1) :
    ‖cmp116SourcePi4FullComplexR2Matrix
        (R := R) anchor K hc hmass hK sigma‖ ≤
      cmp116SourcePi4PhysicalComplexR2RowBound
        K Delta Ahead rho rate radius Rweak := by
  let covarianceDefect :=
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
          (R := R) anchor K hc hmass hK sigma -
      cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
          (R := R) anchor K hc hmass hK (fun _ => 1)
  let covarianceDefectBound :=
    cmp116SourcePi4PhysicalComplexContourDefectBound
      Nc Delta Ahead rho rate radius Rweak
  let precisionRow := ‖cmp116PhysicalEndomorphismComplexMatrix K‖
  let relativeDefect :=
    ‖cmp116PhysicalEndomorphismComplexMatrix K * covarianceDefect‖
  let relativeDefectBound := precisionRow * covarianceDefectBound
  have hcovarianceDefect :
      ‖covarianceDefect‖ ≤ covarianceDefectBound := by
    simpa [covarianceDefect, covarianceDefectBound,
      cmp116SourcePi4PhysicalComplexContourDefectBound, inv_pow] using
      (linfty_opNorm_cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_sub_one_le
        anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri
        hsourceRange hDelta hDelta1 sigma hradius hRweak hdiff hcap hseries)
  have hrelative : relativeDefect ≤ relativeDefectBound := by
    calc
      relativeDefect ≤ precisionRow * ‖covarianceDefect‖ :=
        Matrix.linfty_opNorm_mul _ _
      _ ≤ precisionRow * covarianceDefectBound :=
        mul_le_mul_of_nonneg_left hcovarianceDefect (norm_nonneg _)
  have hrelativeSmall : relativeDefect < 1 :=
    hrelative.trans_lt (by
      simpa [relativeDefectBound, precisionRow, covarianceDefectBound]
        using hneumann)
  have hraw :=
    linfty_opNorm_cmp116SourcePi4FullComplexR2Matrix_le
      anchor K hsourceRange hfiniteRange hc hmass hK hD sigma
      (by simpa [relativeDefect, covarianceDefect] using hrelativeSmall)
  have hboundSmall : relativeDefectBound < 1 := by
    simpa [relativeDefectBound, precisionRow, covarianceDefectBound]
      using hneumann
  have hinv :
      (1 - relativeDefect)⁻¹ ≤ (1 - relativeDefectBound)⁻¹ := by
    exact
      (inv_le_inv₀ (by linarith [hrelativeSmall])
        (by linarith [hboundSmall])).2 (by linarith)
  have hprecisionRow : 0 ≤ precisionRow := norm_nonneg _
  have hinvBound : 0 ≤ (1 - relativeDefectBound)⁻¹ := by
    exact inv_nonneg.mpr (by linarith [hboundSmall])
  change ‖cmp116SourcePi4FullComplexR2Matrix
      (R := R) anchor K hc hmass hK sigma‖ ≤
    ((1 - relativeDefectBound)⁻¹ * precisionRow) *
      covarianceDefectBound * precisionRow
  calc
    ‖cmp116SourcePi4FullComplexR2Matrix
        (R := R) anchor K hc hmass hK sigma‖ ≤
        ((1 - relativeDefect)⁻¹ * precisionRow) *
          ‖covarianceDefect‖ * precisionRow := by
      simpa [relativeDefect, covarianceDefect, precisionRow] using hraw
    _ ≤ ((1 - relativeDefectBound)⁻¹ * precisionRow) *
          covarianceDefectBound * precisionRow := by
      apply mul_le_mul_of_nonneg_right _ hprecisionRow
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hinv hprecisionRow
      · exact hcovarianceDefect
      · exact norm_nonneg _
      · exact mul_nonneg hinvBound hprecisionRow

end

end YangMills.RG
