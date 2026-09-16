/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourceRestrictedConditionedPhysicalR3SourceRate

/-!
# Source-specific producer of the conditioned `R3` rate

This module instantiates the short bilateral bridge with the physical
row/column estimates.  The outer carrier is `Z`; `Z0` remains the inner-field
and complement region.  No support condition is imposed on the covariance
root.
-/

namespace YangMills.RG

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- Uniform deviation of the restricted shifted source coupling. -/
theorem norm_cmp116SourceRestrictedShiftedCoupling_sub_one_le_radius
    {n : ℕ} {Delta : Type*} [DecidableEq Delta]
    (carrier : Finset Delta) (e : Fin n ≃ ↥carrier)
    (radius : Fin n → ℝ) (radiusBound : ℝ)
    (hradiusBound : 0 ≤ radiusBound)
    (hradiusCap : ∀ i, 1 + radius i ≤ radiusBound)
    (z : Fin n → ℂ)
    (hz : CMP116Eq214ShiftedPolydisc n radius z)
    (d : Delta) :
    ‖cmp116SourceRestrictedShiftedCoupling carrier e z d - 1‖ ≤
      radiusBound := by
  by_cases hd : d ∈ carrier
  · exact
      (norm_cmp116SourceRestrictedShiftedCoupling_sub_one_le
        carrier e radius z hz hd).trans
          (hradiusCap (e.symm ⟨d, hd⟩))
  · rw [norm_cmp116SourceRestrictedShiftedCoupling_sub_one_of_not_mem
      carrier e z hd]
    exact hradiusBound

/-- Uniform norm of the restricted shifted source coupling. -/
theorem norm_cmp116SourceRestrictedShiftedCoupling_le_one_add_radius
    {n : ℕ} {Delta : Type*} [DecidableEq Delta]
    (carrier : Finset Delta) (e : Fin n ≃ ↥carrier)
    (radius : Fin n → ℝ) (radiusBound : ℝ)
    (hradiusBound : 0 ≤ radiusBound)
    (hradiusCap : ∀ i, 1 + radius i ≤ radiusBound)
    (z : Fin n → ℂ)
    (hz : CMP116Eq214ShiftedPolydisc n radius z)
    (d : Delta) :
    ‖cmp116SourceRestrictedShiftedCoupling carrier e z d‖ ≤
      1 + radiusBound := by
  calc
    ‖cmp116SourceRestrictedShiftedCoupling carrier e z d‖
        ≤ ‖cmp116SourceRestrictedShiftedCoupling carrier e z d - 1‖ + 1 := by
          simpa using norm_add_le
            (cmp116SourceRestrictedShiftedCoupling carrier e z d - 1)
            (1 : ℂ)
    _ ≤ radiusBound + 1 := by
      gcongr
      exact
        norm_cmp116SourceRestrictedShiftedCoupling_sub_one_le_radius
          carrier e radius radiusBound hradiusBound hradiusCap z hz d
    _ = 1 + radiusBound := by ring

namespace CMP116Eq214PhysicalContourDensity

/-- The `R3` matrix of the physical restricted constructor is the literal
source matrix evaluated at the shifted local coupling. -/
@[simp]
theorem withSourcePi4RestrictedComplexGaussianOfPhysicalContour_r3Matrix
    {nDelta nY M Q Nc R Delta : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    {Site E : Type*} {Psi Phi : Site → Type*} [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond 4 (M * (2 * Q))) Site Psi Phi E (Nc ^ 2 - 1))
    (anchor : FinBox 4 Q)
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (hcarrier : contourCarrier ⊆ cmp116SourceSigmaZero anchor)
    (e : Fin nDelta ≃ ↥contourCarrier)
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (K root : PhysicalEndomorphism M Q Nc)
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
    {Ahead rho rate radius : ℝ}
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
    (hDelta : ∀ y, (cmp116CoarseFaceAdj 4 Q).degree y ≤ Delta)
    (hDelta1 : 1 ≤ Delta)
    (hradius : 0 ≤ radius)
    (hradiusCap : ∀ i, 1 + C.deltaRadius i ≤ radius)
    (hseries :
      ‖cmp116SourcePi4ComplexContourRatio
        Delta rho (1 + radius)‖ < 1)
    (hneumann :
      ‖cmp116PhysicalEndomorphismComplexMatrix K‖ *
        cmp116SourcePi4PhysicalComplexContourDefectBound
          Nc Delta Ahead rho rate radius (1 + radius) < 1)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    (C.withSourcePi4RestrictedComplexGaussianOfPhysicalContour
      anchor contourCarrier hcarrier e Z0 K root
      hsourceRange hfiniteRange hc hmass hK hD
      hAhead hrho hrate hgeom Cert htri hDelta hDelta1
      hradius hradiusCap hseries hneumann).r3Matrix sigma tau psi phi =
      cmp116SourcePi4FullComplexR3Matrix
        (R := R) anchor K root hc hmass hK Z0
          (cmp116SourceRestrictedShiftedCoupling
            contourCarrier e sigma) := by
  rfl

set_option maxHeartbeats 12000000 in
/-- The physical row and column budgets generate the exact source rate on
the conditioned outer activity carrier `Z`. -/
theorem dotProduct_sourcePi4RestrictedConditioned_r3RealSource_self_le_physical
    {nDelta nY M Q Nc R Delta L lieDim : ℕ}
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
    {Ahead rho rate radius : ℝ}
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
    (hDelta : ∀ y, (cmp116CoarseFaceAdj 4 Q).degree y ≤ Delta)
    (hDelta1 : 1 ≤ Delta)
    (hradius : 0 ≤ radius)
    (hradiusCap : ∀ i, 1 + C.deltaRadius i ≤ radius)
    (hseries :
      ‖cmp116SourcePi4ComplexContourRatio
        Delta rho (1 + radius)‖ < 1)
    (hneumann :
      ‖cmp116PhysicalEndomorphismComplexMatrix K‖ *
        cmp116SourcePi4PhysicalComplexContourDefectBound
          Nc Delta Ahead rho rate radius (1 + radius) < 1)
    (hneumannTranspose :
      cmp116SourcePi4PhysicalComplexTransposeRelativeDefectBound
        K Delta Ahead rho rate radius (1 + radius) < 1)
    (sigma : Fin nDelta → ℂ)
    (hsigma : CMP116Eq214ShiftedPolydisc nDelta C.deltaRadius sigma)
    (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (x : CMP116Eq214GaussianCoordinate
      (PhysicalBond 4 (M * (2 * Q))) (Nc ^ 2 - 1)) :
    let Craw :=
      C.withSourcePi4RestrictedComplexGaussianOfPhysicalContour
        anchor contourCarrier hcarrier e Z0 K root
        hsourceRange hfiniteRange hc hmass hK hD
        hAhead hrho hrate hgeom Cert htri hDelta hDelta1
        hradius hradiusCap hseries hneumann
    let Csource :=
      Craw.withConditionedOuterCarrier
        (cmp116SourcePhysicalLocalizedCoordinates Dict Z)
    Csource.r3RealSource sigma tau psi phi x ⬝ᵥ
        Csource.r3RealSource sigma tau psi phi x ≤
      cmp116SourcePi4PhysicalComplexR3SourceRate
          K root Z0 Delta Ahead rho rate radius (1 + radius) *
        ∑ i ∈ cmp116SourcePhysicalLocalizedCoordinates Dict Z, x i ^ 2 := by
  dsimp only
  let Craw :=
    C.withSourcePi4RestrictedComplexGaussianOfPhysicalContour
      anchor contourCarrier hcarrier e Z0 K root
      hsourceRange hfiniteRange hc hmass hK hD
      hAhead hrho hrate hgeom Cert htri hDelta hDelta1
      hradius hradiusCap hseries hneumann
  have hsource :=
    Craw.dotProduct_conditionedOuterCarrier_r3RealSource_self_le_bilateral
      (cmp116SourcePhysicalLocalizedCoordinates Dict Z)
      sigma tau psi phi x
  rw [C.withSourcePi4RestrictedComplexGaussianOfPhysicalContour_r3Matrix
    anchor contourCarrier hcarrier e Z0 K root
    hsourceRange hfiniteRange hc hmass hK hD
    hAhead hrho hrate hgeom Cert htri hDelta hDelta1
    hradius hradiusCap hseries hneumann] at hsource
  have hdiff : ∀ d,
      ‖cmp116SourceRestrictedShiftedCoupling
        contourCarrier e sigma d - 1‖ ≤ radius :=
    norm_cmp116SourceRestrictedShiftedCoupling_sub_one_le_radius
      contourCarrier e C.deltaRadius radius hradius hradiusCap sigma hsigma
  have hcap : ∀ d,
      ‖cmp116SourceRestrictedShiftedCoupling contourCarrier e sigma d‖ ≤
        1 + radius :=
    norm_cmp116SourceRestrictedShiftedCoupling_le_one_add_radius
      contourCarrier e C.deltaRadius radius hradius hradiusCap sigma hsigma
  have hrow :=
    linfty_opNorm_cmp116SourcePi4FullComplexR3Matrix_le_physical
      anchor K root hsourceRange hfiniteRange hc hmass hK hD
      Z0 hAhead hrho hrate hgeom Cert htri hDelta hDelta1
      (cmp116SourceRestrictedShiftedCoupling contourCarrier e sigma)
      hradius (by linarith) hdiff hcap hseries hneumann
  have hcolumn :=
    linfty_opNorm_transpose_cmp116SourcePi4FullComplexR3Matrix_le_physical
      anchor K root hsourceRange hfiniteRange hc hmass hK hD
      Z0 hAhead hrho hrate hgeom Cert htri hDelta hDelta1
      (cmp116SourceRestrictedShiftedCoupling contourCarrier e sigma)
      hradius (by linarith) hdiff hcap hseries hneumannTranspose
  calc
    _ ≤
        ‖cmp116SourcePi4FullComplexR3Matrix
            (R := R) anchor K root hc hmass hK Z0
            (cmp116SourceRestrictedShiftedCoupling contourCarrier e sigma)‖ *
          ‖(cmp116SourcePi4FullComplexR3Matrix
            (R := R) anchor K root hc hmass hK Z0
            (cmp116SourceRestrictedShiftedCoupling
              contourCarrier e sigma)).transpose‖ *
          ∑ i ∈ cmp116SourcePhysicalLocalizedCoordinates Dict Z, x i ^ 2 :=
      hsource
    _ ≤
        cmp116SourcePi4PhysicalComplexR3SourceRate
            K root Z0 Delta Ahead rho rate radius (1 + radius) *
          ∑ i ∈ cmp116SourcePhysicalLocalizedCoordinates Dict Z, x i ^ 2 := by
      unfold cmp116SourcePi4PhysicalComplexR3SourceRate
      have hrowNonneg :
          0 ≤ cmp116SourcePi4PhysicalComplexR3RowBound
            K root Z0 Delta Ahead rho rate radius (1 + radius) :=
        (norm_nonneg _).trans hrow
      have hcolumnNonneg :
          0 ≤ cmp116SourcePi4PhysicalComplexR3ColumnBound
            K root Z0 Delta Ahead rho rate radius (1 + radius) :=
        (norm_nonneg _).trans hcolumn
      gcongr

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
