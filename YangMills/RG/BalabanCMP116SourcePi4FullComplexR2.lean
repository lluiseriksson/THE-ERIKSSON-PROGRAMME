/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4PhysicalComplexContourNonsingularity

/-!
# Literal source-complex `R2`

The source sign is `R2 = K0 - Ksigma`.  Here `K0` is the original physical
precision matrix and `Ksigma` is the inverse of the complete weakened source
covariance.  The terminal theorem proves the exact resolvent identity from
the already established physical contour conditions.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- Literal full-source complex correction with the CMP116 sign
`R2 = K0 - Ksigma`. -/
noncomputable def cmp116SourcePi4FullComplexR2Matrix
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ) :
    Matrix
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ :=
  cmp116PhysicalEndomorphismComplexMatrix K -
    cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
      (R := R) anchor K hc hmass hK sigma

/-- Algebraic resolvent identity in the exact orientation needed by the
source correction. -/
theorem Matrix.sub_eq_leftInv_mul_sub_mul_of_inverse_laws
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P0 P1 C0 C1 : Matrix ι ι ℂ)
    (hbaseRight : C0 * P0 = 1)
    (htargetLeft : P1 * C1 = 1) :
    P0 - P1 = P1 * (C1 - C0) * P0 := by
  calc
    P0 - P1 = 1 * P0 - P1 * 1 := by rw [one_mul, mul_one]
    _ = (P1 * C1) * P0 - P1 * (C0 * P0) := by
      rw [htargetLeft, hbaseRight]
    _ = P1 * (C1 - C0) * P0 := by
      noncomm_ring

/-- Under the explicit physical source-contour conditions, `R2` is exactly
the resolvent product of the contour covariance defect. -/
theorem cmp116SourcePi4FullComplexR2Matrix_eq_resolventProduct
    {M Q Nc R Δ : ℕ}
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
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hdiff : ∀ d, ‖sigma d - 1‖ ≤ radius)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (hseries :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hneumann :
      ‖cmp116PhysicalEndomorphismComplexMatrix K‖ *
        cmp116SourcePi4PhysicalComplexContourDefectBound
          Nc Δ Ahead rho rate radius Rweak < 1) :
    cmp116SourcePi4FullComplexR2Matrix
        (R := R) anchor K hc hmass hK sigma =
      cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
          (R := R) anchor K hc hmass hK sigma *
        (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
            (R := R) anchor K hc hmass hK sigma -
          cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
            (R := R) anchor K hc hmass hK (fun _ => 1)) *
        cmp116PhysicalEndomorphismComplexMatrix K := by
  let C0 :=
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
      (R := R) anchor K hc hmass hK (fun _ => 1)
  let C1 :=
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
      (R := R) anchor K hc hmass hK sigma
  let P0 := cmp116PhysicalEndomorphismComplexMatrix K
  let P1 :=
    cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
      (R := R) anchor K hc hmass hK sigma
  have hbaseLeft : P0 * C0 = 1 := by
    dsimp [P0, C0]
    rw [
      cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_one_eq_exact
        anchor K hsourceRange hfiniteRange hc hmass hK hD]
    exact
      cmp116SourcePi4Quotient_precision_mul_exactCovarianceMatrix_eq_one
        K hc hmass hK hD
  have hbaseDet : C0.det ≠ 0 := by
    dsimp [C0]
    exact
      cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_one_det_ne_zero
        anchor K hsourceRange hfiniteRange hc hmass hK hD
  have hbaseInv : C0⁻¹ = P0 :=
    Matrix.inv_eq_left_inv hbaseLeft
  have hbaseRight : C0 * P0 = 1 := by
    rw [← hbaseInv]
    exact Matrix.mul_nonsing_inv C0 (isUnit_iff_ne_zero.mpr hbaseDet)
  have htargetLeft : P1 * C1 = 1 := by
    dsimp [P1, C1]
    exact
      cmp116SourcePi4_fullComplexPrecision_mul_covariance_eq_one_of_physicalContour
        anchor K hsourceRange hfiniteRange hc hmass hK hD
        hAhead hrho hrate hgeom Cert htri hΔ hΔ1 sigma hradius hRweak
        hdiff hcap hseries hneumann
  change P0 - P1 = P1 * (C1 - C0) * P0
  exact Matrix.sub_eq_leftInv_mul_sub_mul_of_inverse_laws
    P0 P1 C0 C1 hbaseRight htargetLeft

end

end YangMills.RG
