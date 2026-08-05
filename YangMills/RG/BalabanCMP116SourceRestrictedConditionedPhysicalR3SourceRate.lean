/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourceRestrictedConditionedPhysicalContour
import YangMills.RG.BalabanCMP116SourcePi4FullComplexR3BilateralNorm

/-!
# Physical source rate on the conditioned CMP116 outer carrier

PRE-VALIDATION: the new source-rate nonnegativity producer is present, its
updated `.olean` has not yet been materialized, and the theorem has not yet
been checked by the compiler.

Equation (2.23) restricts the outer Gaussian to the activity carrier `Z`.
The literal `R3` operator remains global, while its row and column norms are
controlled by the physical source construction.  This file records the short
bilateral bridge; the large physical producer is kept in a separate module.
-/

namespace YangMills.RG

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- The explicit source rate produced by the physical row and column
budgets of the literal complex `R3`. -/
noncomputable def cmp116SourcePi4PhysicalComplexR3SourceRate
    {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (K root : PhysicalEndomorphism M Q Nc)
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (Delta : ℕ) (Ahead rho rate radius Rweak : ℝ) : ℝ :=
  cmp116SourcePi4PhysicalComplexR3RowBound
      K root Z0 Delta Ahead rho rate radius Rweak *
    cmp116SourcePi4PhysicalComplexR3ColumnBound
      K root Z0 Delta Ahead rho rate radius Rweak

/-- The literal source-energy rate is nonnegative under the same row and
transpose Neumann windows used by its physical `R2` factors.  This theorem
exposes a sign consequence of the existing contour hypotheses; it does not
add an independent source-rate assumption. -/
theorem cmp116SourcePi4PhysicalComplexR3SourceRate_nonneg
    {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (K root : PhysicalEndomorphism M Q Nc)
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (Delta : ℕ) {Ahead rho rate radius Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hradius : 0 ≤ radius)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (hneumann :
      ‖cmp116PhysicalEndomorphismComplexMatrix K‖ *
        cmp116SourcePi4PhysicalComplexContourDefectBound
          Nc Delta Ahead rho rate radius Rweak < 1)
    (hneumannTranspose :
      cmp116SourcePi4PhysicalComplexTransposeRelativeDefectBound
        K Delta Ahead rho rate radius Rweak < 1) :
    0 ≤ cmp116SourcePi4PhysicalComplexR3SourceRate
      K root Z0 Delta Ahead rho rate radius Rweak := by
  let defect :=
    cmp116SourcePi4PhysicalComplexContourDefectBound
      Nc Delta Ahead rho rate radius Rweak
  have hgeometric :
      0 ≤ cmp99PhysicalBondGeometricRowSum 4 rate :=
    cmp99PhysicalBondGeometricRowSum_nonneg hgeom
  have hdefect : 0 ≤ defect := by
    dsimp [defect, cmp116SourcePi4PhysicalComplexContourDefectBound,
      cmp116SourcePi4ComplexContourPrefactor]
    positivity
  have hrowInv :
      0 ≤ (1 -
        ‖cmp116PhysicalEndomorphismComplexMatrix K‖ * defect)⁻¹ := by
    apply inv_nonneg.mpr
    linarith
  have hcolumnInv :
      0 ≤ (1 -
        ‖(cmp116PhysicalEndomorphismComplexMatrix K).transpose‖ *
          defect)⁻¹ := by
    apply inv_nonneg.mpr
    have hsmall :
        ‖(cmp116PhysicalEndomorphismComplexMatrix K).transpose‖ *
          defect < 1 := by
      simpa [defect,
        cmp116SourcePi4PhysicalComplexTransposeRelativeDefectBound] using
        hneumannTranspose
    linarith
  have hR2row :
      0 ≤ cmp116SourcePi4PhysicalComplexR2RowBound
        K Delta Ahead rho rate radius Rweak := by
    change 0 ≤
      ((1 - ‖cmp116PhysicalEndomorphismComplexMatrix K‖ * defect)⁻¹ *
        ‖cmp116PhysicalEndomorphismComplexMatrix K‖) * defect *
          ‖cmp116PhysicalEndomorphismComplexMatrix K‖
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hrowInv (norm_nonneg _)) hdefect)
      (norm_nonneg _)
  have hR2column :
      0 ≤ cmp116SourcePi4PhysicalComplexR2ColumnBound
        K Delta Ahead rho rate radius Rweak := by
    change 0 ≤
      ((1 -
          ‖(cmp116PhysicalEndomorphismComplexMatrix K).transpose‖ * defect)⁻¹ *
        ‖(cmp116PhysicalEndomorphismComplexMatrix K).transpose‖) * defect *
          ‖(cmp116PhysicalEndomorphismComplexMatrix K).transpose‖
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hcolumnInv (norm_nonneg _)) hdefect)
      (norm_nonneg _)
  have hR3row :
      0 ≤ cmp116SourcePi4PhysicalComplexR3RowBound
        K root Z0 Delta Ahead rho rate radius Rweak := by
    unfold cmp116SourcePi4PhysicalComplexR3RowBound
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (norm_nonneg _) hR2row)
        (norm_nonneg _))
      (norm_nonneg _)
  have hR3column :
      0 ≤ cmp116SourcePi4PhysicalComplexR3ColumnBound
        K root Z0 Delta Ahead rho rate radius Rweak := by
    unfold cmp116SourcePi4PhysicalComplexR3ColumnBound
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        hR2column)
      (norm_nonneg _)
  unfold cmp116SourcePi4PhysicalComplexR3SourceRate
  exact mul_nonneg hR3row hR3column

namespace CMP116Eq214PhysicalContourDensity

/-- Bilateral row and column estimates for the literal source operator imply
the exact carrier-localized source-energy bound. -/
theorem dotProduct_sourcePi4RestrictedConditioned_r3RealSource_self_le_of_bilateral
    {nDelta nY M Q Nc R L lieDim : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero L] [NeZero lieDim]
    {Site E : Type*} {Psi Phi : Site → Type*} [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond 4 (M * (2 * Q))) Site Psi Phi E (Nc ^ 2 - 1))
    (Dict : PhysicalGaugeCMP116Dictionary
      4 (M * (2 * Q)) Nc 4 L lieDim)
    (anchor : FinBox 4 Q)
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (hcarrier : contourCarrier ⊆ cmp116SourceSigmaZero anchor)
    (e : Fin nDelta ≃ ↥contourCarrier)
    (Z0 Z : Finset (FinBox 4 (2 * Q)))
    (K root : PhysicalEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          hc hmass hK‖ < 1)
    (hcontour : ∀ z,
      CMP116Eq214ShiftedPolydisc nDelta C.deltaRadius z →
      (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
          (R := R) anchor K hc hmass hK
          (cmp116SourceRestrictedShiftedCoupling
            contourCarrier e z)).det ≠ 0)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (x : CMP116Eq214GaussianCoordinate
      (PhysicalBond 4 (M * (2 * Q))) (Nc ^ 2 - 1))
    {rowBound columnBound : ℝ}
    (hrow :
      ‖cmp116SourcePi4FullComplexR3Matrix
          (R := R) anchor K root hc hmass hK Z0
          (cmp116SourceRestrictedShiftedCoupling
            contourCarrier e sigma)‖ ≤ rowBound)
    (hcolumn :
      ‖(cmp116SourcePi4FullComplexR3Matrix
          (R := R) anchor K root hc hmass hK Z0
          (cmp116SourceRestrictedShiftedCoupling
            contourCarrier e sigma)).transpose‖ ≤ columnBound) :
    let Csource :=
      C.withSourcePi4RestrictedConditionedComplexGaussian Dict
        anchor contourCarrier hcarrier e Z0 Z K root
        hsourceRange hrange hc hmass hK hD hcontour
    Csource.r3RealSource sigma tau psi phi x ⬝ᵥ
        Csource.r3RealSource sigma tau psi phi x ≤
      rowBound * columnBound *
        ∑ i ∈ cmp116SourcePhysicalLocalizedCoordinates Dict Z, x i ^ 2 := by
  dsimp only
  let Craw :=
    C.withSourcePi4RestrictedComplexGaussian
      anchor contourCarrier hcarrier e Z0 K root
      hsourceRange hrange hc hmass hK hD hcontour
  have h :=
    Craw.dotProduct_conditionedOuterCarrier_r3RealSource_self_le_bilateral
      (cmp116SourcePhysicalLocalizedCoordinates Dict Z)
      sigma tau psi phi x
  rw [C.withSourcePi4RestrictedComplexGaussian_r3Matrix
    anchor contourCarrier hcarrier e Z0 K root
    hsourceRange hrange hc hmass hK hD hcontour] at h
  calc
    _ ≤
        ‖cmp116SourcePi4FullComplexR3Matrix
            (R := R) anchor K root hc hmass hK Z0
            (cmp116SourceRestrictedShiftedCoupling
              contourCarrier e sigma)‖ *
          ‖(cmp116SourcePi4FullComplexR3Matrix
            (R := R) anchor K root hc hmass hK Z0
            (cmp116SourceRestrictedShiftedCoupling
              contourCarrier e sigma)).transpose‖ *
          ∑ i ∈ cmp116SourcePhysicalLocalizedCoordinates Dict Z, x i ^ 2 := h
    _ ≤ rowBound * columnBound *
          ∑ i ∈ cmp116SourcePhysicalLocalizedCoordinates Dict Z, x i ^ 2 := by
      have hrowNonneg : 0 ≤ rowBound := (norm_nonneg _).trans hrow
      have hcolumnNonneg : 0 ≤ columnBound :=
        (norm_nonneg _).trans hcolumn
      gcongr

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
