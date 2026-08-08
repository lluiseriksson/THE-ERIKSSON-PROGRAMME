/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourceRestrictedContourDensityTraceBound
import YangMills.RG.BalabanCMP116SourcePi4PhysicalComplexContourNonsingularity

/-!
# A uniform determinant cost on the restricted source contour

The localized determinant estimate originally retained the norm of the
contour-dependent relative covariance defect in its exponent.  This module
replaces that norm by the explicit, source-generated contour defect bound.
The resulting determinant constant is uniform on the whole Cauchy
polydisc and remains independent of the ambient volume.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- Monotonicity of the source determinant cost in the defect norm, on the
physical interval below the Neumann threshold. -/
theorem cmp116SourceRestrictedContourDeterminantPerCarrierCost_mono_defect
    (M Nc Delta : ℕ)
    {radius Rweak rate Ahead rho precisionNorm defectNorm defectBound : ℝ}
    (hradius : 0 ≤ radius)
    (hAhead : 0 ≤ Ahead)
    (hprecision : 0 ≤ precisionNorm)
    (hgeom :
      0 ≤ ((Nc ^ 2 - 1 : ℕ) : ℝ) *
        cmp99PhysicalBondGeometricRowSum 4 rate)
    (hle : defectNorm ≤ defectBound)
    (hbound : defectBound < 1) :
    cmp116SourceRestrictedContourDeterminantPerCarrierCost
        M Nc Delta radius Rweak rate Ahead rho precisionNorm defectNorm ≤
      cmp116SourceRestrictedContourDeterminantPerCarrierCost
        M Nc Delta radius Rweak rate Ahead rho precisionNorm defectBound := by
  let geometricRow : ℝ :=
    ((Nc ^ 2 - 1 : ℕ) : ℝ) *
      cmp99PhysicalBondGeometricRowSum 4 rate
  let walkRatio : ℝ :=
    cmp116SourcePi4ComplexContourRatio Delta rho Rweak
  let numerator : ℝ :=
    (625 *
      (((40000 * M ^ 4) * (Nc ^ 2 - 1) : ℕ) : ℝ) *
      (radius * Rweak ^ 10000) * geometricRow *
      precisionNorm * (Ahead * geometricRow)) *
      (1 - walkRatio)⁻¹ ^ 2
  have hnumerator : 0 ≤ numerator := by
    dsimp [numerator]
    positivity
  have hdenBound : 0 < 1 - defectBound := by linarith
  have hden : 0 < 1 - defectNorm := by linarith
  have hinv :
      (1 - defectNorm)⁻¹ ≤ (1 - defectBound)⁻¹ := by
    exact (inv_le_inv₀ hden hdenBound).2 (by linarith)
  change (numerator / (1 - defectNorm)) / 2 ≤
    (numerator / (1 - defectBound)) / 2
  gcongr

/-- Uniform source-generated determinant cost.  The defect norm appearing
in the earlier pointwise cost is replaced by its explicit physical contour
majorant. -/
noncomputable def cmp116SourceRestrictedUniformContourDeterminantCost
    (M Nc Delta : ℕ)
    (radius Rweak rate Ahead rho precisionNorm : ℝ) : ℝ :=
  cmp116SourceRestrictedContourDeterminantPerCarrierCost
    M Nc Delta radius Rweak rate Ahead rho precisionNorm
      (precisionNorm *
        cmp116SourcePi4PhysicalComplexContourDefectBound
          Nc Delta Ahead rho rate radius Rweak)

set_option maxHeartbeats 6000000 in
/-- The restricted determinant density is bounded uniformly over the source
contour by one carrier-linear exponential whose coefficient is constructed
from the physical walk certificate and the Neumann defect majorant. -/
theorem norm_cmp116SourceRestrictedContour_logDetDensity_le_exp_uniformCost_card
    {q M Q Nc R Delta : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (carrier Z0 : Finset (FinBox 4 (2 * Q)))
    (hcarrierZ0 : carrier ⊆ Z0)
    (e : Fin q ≃ ↥carrier) (z : Fin q → ℂ)
    (K : PhysicalEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hfiniteRange :
      PhysicalCovarianceFiniteRange K physicalBondDist R)
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
      (cmp99SourcePi4ChartCore (M := M)) hc hmass hK
      physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle +
          physicalBondDist middle source)
    (hDelta : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Delta)
    (hDelta1 : 1 ≤ Delta)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hz : ∀ i, ‖z i‖ ≤ radius)
    (hcap : ∀ i, ‖1 + z i‖ ≤ Rweak)
    (hcontourSmall :
      ‖cmp116SourcePi4ComplexContourRatio Delta rho Rweak‖ < 1)
    (hneumann :
      ‖cmp116PhysicalEndomorphismComplexMatrix K‖ *
        cmp116SourcePi4PhysicalComplexContourDefectBound
          Nc Delta Ahead rho rate radius Rweak < 1) :
    ‖cmp116Eq214LogDeterminantDensity
        (cmp116PhysicalEndomorphismComplexMatrix K)
        (cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
          (R := R) anchor K hc hmass hK
            (cmp116SourceRestrictedShiftedCoupling carrier e z))‖ ≤
      Real.exp
        (cmp116SourceRestrictedUniformContourDeterminantCost
          M Nc Delta radius Rweak rate Ahead rho
          ‖cmp116PhysicalEndomorphismComplexMatrix K‖ *
          (Z0.card : ℝ)) := by
  let defect :=
    cmp116SourcePi4FullComplexRelativeCovarianceDefect
      (R := R) anchor K hc hmass hK
        (cmp116SourceRestrictedShiftedCoupling carrier e z)
  let defectBound :=
    ‖cmp116PhysicalEndomorphismComplexMatrix K‖ *
      cmp116SourcePi4PhysicalComplexContourDefectBound
        Nc Delta Ahead rho rate radius Rweak
  have hsigmaDiff : ∀ d,
      ‖cmp116SourceRestrictedShiftedCoupling carrier e z d - 1‖ ≤
        radius := by
    intro d
    by_cases hd : d ∈ carrier
    · simpa [
        norm_cmp116SourceRestrictedShiftedCoupling_sub_one_of_mem
          carrier e z hd] using hz (e.symm ⟨d, hd⟩)
    · rw [norm_cmp116SourceRestrictedShiftedCoupling_sub_one_of_not_mem
        carrier e z hd]
      exact hradius
  have hsigmaCap : ∀ d,
      ‖cmp116SourceRestrictedShiftedCoupling carrier e z d‖ ≤ Rweak := by
    intro d
    by_cases hd : d ∈ carrier
    · simpa [cmp116SourceRestrictedShiftedCoupling, hd] using
        hcap (e.symm ⟨d, hd⟩)
    · rw [cmp116SourceRestrictedShiftedCoupling_eq_one_of_not_mem
        carrier e z hd, norm_one]
      exact hRweak
  have hdefectLe : ‖defect‖ ≤ defectBound := by
    simpa [defect, defectBound] using
      (linfty_opNorm_cmp116SourcePi4FullComplexRelativeCovarianceDefect_le
        anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri
        hsourceRange hDelta hDelta1
        (cmp116SourceRestrictedShiftedCoupling carrier e z)
        hradius hRweak hsigmaDiff hsigmaCap hcontourSmall)
  have hdefectSmall : ‖defect‖ < 1 :=
    hdefectLe.trans_lt (by simpa [defectBound] using hneumann)
  have hpointwise :=
    norm_cmp116SourceRestrictedContour_logDetDensity_le_exp_detCost_card
      anchor carrier Z0 hcarrierZ0 e z K
      hsourceRange hfiniteRange hc hmass hK hD
      hAhead hrho Cert hrate hgeom htri hDelta hDelta1
      radius Rweak hradius hRweak hz hcap hcontourSmall
      (by simpa [defect] using hdefectSmall)
  have hcost :
      cmp116SourceRestrictedContourDeterminantPerCarrierCost
          M Nc Delta radius Rweak rate Ahead rho
          ‖cmp116PhysicalEndomorphismComplexMatrix K‖ ‖defect‖ ≤
        cmp116SourceRestrictedUniformContourDeterminantCost
          M Nc Delta radius Rweak rate Ahead rho
          ‖cmp116PhysicalEndomorphismComplexMatrix K‖ := by
    apply
      cmp116SourceRestrictedContourDeterminantPerCarrierCost_mono_defect
    · exact hradius
    · exact hAhead
    · exact norm_nonneg _
    · exact mul_nonneg (by positivity)
        (cmp99PhysicalBondGeometricRowSum_nonneg hgeom)
    · exact hdefectLe
    · simpa [defectBound] using hneumann
  exact hpointwise.trans (by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hcost (by positivity))

end

end YangMills.RG
