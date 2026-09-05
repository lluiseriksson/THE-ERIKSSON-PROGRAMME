/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4PhysicalContourDensity
import YangMills.RG.BalabanCMP116SourceRestrictedShiftedComplexContour

/-!
# Install a localized source `Pi⁴` complex Gaussian

The older source constructor identifies the Cauchy coordinates with every
weakening cube in the periodic volume.  A localized equation-(2.14) term must
instead vary only the physical gap carrier indexed by its `sigma(Delta)`
derivatives.  This constructor makes that locality part of the type:

`e : Fin nDelta ≃ ↥contourCarrier`.

Consequently `nDelta = contourCarrier.card`; no ambient-volume contour
dimension can be passed accidentally.  The contour carrier and the
localization region `Z₀` are deliberately separate: equation (2.26)
identifies `nDelta` with a normalized gap cardinality, whereas `Z₀` controls
the physical Gamma projection.  Outside the contour carrier the source
weakening is exactly one.  This module installs that literal coupling in the
complete complex covariance, precision, Gamma, and logarithmic determinant
density.  It proves no determinant or `R₁` bound.
-/

namespace YangMills.RG

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

namespace CMP116Eq214PhysicalContourDensity

/-- Install the complete source-specific complex Gaussian using only the
localized physical gap coordinates, while retaining the separate `Z₀`
projection in Gamma. -/
def withSourcePi4RestrictedComplexGaussian
    {nDelta nY M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    {Site E : Type*} {Psi Phi : Site → Type*} [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond 4 (M * (2 * Q))) Site Psi Phi E (Nc ^ 2 - 1))
    (anchor : FinBox 4 Q)
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (_hcarrier : contourCarrier ⊆ cmp116SourceSigmaZero anchor)
    (e : Fin nDelta ≃ ↥contourCarrier)
    (Z0 : Finset (FinBox 4 (2 * Q)))
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
            contourCarrier e z)).det ≠ 0) :
    CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond 4 (M * (2 * Q))) Site Psi Phi E (Nc ^ 2 - 1) where
  spectatorSupport := C.spectatorSupport
  fluctuationSupport := C.fluctuationSupport
  deltaRadius := C.deltaRadius
  yRadius := C.yRadius
  referenceRoot := cmp116PhysicalEndomorphismRealMatrix root
  baseGamma := fun _ _ =>
    cmp116SourcePi4PhysicalBaseGammaMatrix K root Z0
  contourGamma := fun z _ _ _ =>
    cmp116SourcePi4FullComplexGammaMatrix
      (R := R) anchor K root hc hmass hK Z0
        (cmp116SourceRestrictedShiftedCoupling contourCarrier e z)
  baseCovariance := fun _ _ =>
    cmp116SourcePi4PhysicalBaseCovarianceMatrix K hc hmass hK
  contourCovariance := fun z _ _ _ =>
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
      (R := R) anchor K hc hmass hK
        (cmp116SourceRestrictedShiftedCoupling contourCarrier e z)
  basePrecision := fun _ _ =>
    cmp116PhysicalEndomorphismComplexMatrix K
  contourPrecision := fun z _ _ _ =>
    cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
      (R := R) anchor K hc hmass hK
        (cmp116SourceRestrictedShiftedCoupling contourCarrier e z)
  determinantDensity := fun z _ _ _ =>
    cmp116Eq214LogDeterminantDensity
      (cmp116PhysicalEndomorphismComplexMatrix K)
      (cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
        (R := R) anchor K hc hmass hK
          (cmp116SourceRestrictedShiftedCoupling contourCarrier e z))
  potential := C.potential
  bondField := C.bondField
  threshold := C.threshold
  contourGamma_zero := by
    intro psi phi
    rw [cmp116SourceRestrictedShiftedCoupling_zero]
    exact cmp116SourcePi4FullComplexGammaMatrix_one_eq_physical
      anchor K root hsourceRange hrange hc hmass hK hD Z0
  contourCovariance_zero := by
    intro psi phi
    rw [cmp116SourceRestrictedShiftedCoupling_zero]
    exact cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_one_eq_exact
      anchor K hsourceRange hrange hc hmass hK hD
  contourPrecision_zero := by
    intro psi phi
    rw [cmp116SourceRestrictedShiftedCoupling_zero]
    exact cmp116SourcePi4FullComplexWeakenedPrecisionMatrix_one_eq_physical
      anchor K hsourceRange hrange hc hmass hK hD
  determinantDensity_zero := by
    intro psi phi
    rw [cmp116SourceRestrictedShiftedCoupling_zero]
    rw [cmp116SourcePi4FullComplexWeakenedPrecisionMatrix_one_eq_physical
      anchor K hsourceRange hrange hc hmass hK hD]
    exact cmp116Eq214LogDeterminantDensity_self
      (cmp116PhysicalEndomorphismComplexMatrix K)
  determinantDensity_sq_mul_basePrecision_det := by
    intro z tau psi phi hz htau
    have hbaseCov :
        (cmp116SourcePi4PhysicalBaseCovarianceMatrix K hc hmass hK).det ≠ 0 := by
      unfold cmp116SourcePi4PhysicalBaseCovarianceMatrix
      rw [← cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_one_eq_exact
        (R := R) anchor K hsourceRange hrange hc hmass hK hD]
      exact
        cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_one_det_ne_zero
          (R := R) anchor K hsourceRange hrange hc hmass hK hD
    have hbasePrecision :
        (cmp116PhysicalEndomorphismComplexMatrix K).det ≠ 0 := by
      have hinv :
          (cmp116SourcePi4PhysicalBaseCovarianceMatrix K hc hmass hK)⁻¹ =
            cmp116PhysicalEndomorphismComplexMatrix K := by
        unfold cmp116SourcePi4PhysicalBaseCovarianceMatrix
        exact Matrix.inv_eq_left_inv
          (cmp116SourcePi4Quotient_precision_mul_exactCovarianceMatrix_eq_one
            K hc hmass hK hD)
      rw [← hinv]
      exact isUnit_iff_ne_zero.mp
        (Matrix.isUnit_nonsing_inv_det
          (cmp116SourcePi4PhysicalBaseCovarianceMatrix K hc hmass hK)
          (isUnit_iff_ne_zero.mpr hbaseCov))
    have hcontourPrecision :
        (cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
          (R := R) anchor K hc hmass hK
            (cmp116SourceRestrictedShiftedCoupling
              contourCarrier e z)).det ≠ 0 := by
      unfold cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
      exact isUnit_iff_ne_zero.mp
        (Matrix.isUnit_nonsing_inv_det
          (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
            (R := R) anchor K hc hmass hK
              (cmp116SourceRestrictedShiftedCoupling contourCarrier e z))
          (isUnit_iff_ne_zero.mpr (hcontour z hz)))
    exact cmp116Eq214LogDeterminantDensity_sq_mul_base_det
      (cmp116PhysicalEndomorphismComplexMatrix K)
      (cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
        (R := R) anchor K hc hmass hK
          (cmp116SourceRestrictedShiftedCoupling contourCarrier e z))
      hbasePrecision hcontourPrecision
  potential_zero := C.potential_zero

/-- Source-facing restricted constructor whose contour nonsingularity is
generated by the existing physical Neumann estimate.  The only radius
comparison concerns the localized Cauchy coordinates. -/
def withSourcePi4RestrictedComplexGaussianOfPhysicalContour
    {nDelta nY M Q Nc R Δ : ℕ}
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
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (hradius : 0 ≤ radius)
    (hradiusCap : ∀ i, 1 + C.deltaRadius i ≤ radius)
    (hseries :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho (1 + radius)‖ < 1)
    (hneumann :
      ‖cmp116PhysicalEndomorphismComplexMatrix K‖ *
        cmp116SourcePi4PhysicalComplexContourDefectBound
          Nc Δ Ahead rho rate radius (1 + radius) < 1) :
    CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond 4 (M * (2 * Q))) Site Psi Phi E (Nc ^ 2 - 1) := by
  apply C.withSourcePi4RestrictedComplexGaussian
    anchor contourCarrier hcarrier e Z0 K root
    hsourceRange hfiniteRange hc hmass hK hD
  intro z hz
  apply
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_det_ne_zero_of_physicalContour
      (radius := radius) (Rweak := 1 + radius)
      anchor K hsourceRange hfiniteRange hc hmass hK hD
      hAhead hrho hrate hgeom Cert htri hΔ hΔ1
      (cmp116SourceRestrictedShiftedCoupling contourCarrier e z)
      hradius
      (by linarith)
  · intro d
    exact
      norm_cmp116SourceRestrictedShiftedCoupling_sub_one_le_global
        contourCarrier e C.deltaRadius z hz hradius hradiusCap d
  · intro d
    exact
      norm_cmp116SourceRestrictedShiftedCoupling_le_one_add_global
        contourCarrier e C.deltaRadius z hz hradius hradiusCap d
  · exact hseries
  · exact hneumann

@[simp]
theorem withSourcePi4RestrictedComplexGaussian_determinantDensity
    {nDelta nY M Q Nc R : ℕ}
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
    (z : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    (C.withSourcePi4RestrictedComplexGaussian
      anchor contourCarrier hcarrier e Z0 K root
      hsourceRange hrange hc hmass hK hD hcontour).determinantDensity
        z tau psi phi =
      cmp116Eq214LogDeterminantDensity
        (cmp116PhysicalEndomorphismComplexMatrix K)
        (cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
          (R := R) anchor K hc hmass hK
            (cmp116SourceRestrictedShiftedCoupling contourCarrier e z)) :=
  rfl

@[simp]
theorem withSourcePi4RestrictedComplexGaussian_r1Matrix
    {nDelta nY M Q Nc R : ℕ}
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
    (z : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    (C.withSourcePi4RestrictedComplexGaussian
      anchor contourCarrier hcarrier e Z0 K root
      hsourceRange hrange hc hmass hK hD hcontour).r1Matrix
        z tau psi phi =
      cmp116SourcePi4FullComplexR1Matrix
        (R := R) anchor K root hc hmass hK Z0
          (cmp116SourceRestrictedShiftedCoupling contourCarrier e z) :=
  rfl

@[simp]
theorem withSourcePi4RestrictedComplexGaussian_r2Matrix
    {nDelta nY M Q Nc R : ℕ}
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
    (z : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    (C.withSourcePi4RestrictedComplexGaussian
      anchor contourCarrier hcarrier e Z0 K root
      hsourceRange hrange hc hmass hK hD hcontour).r2Matrix
        z tau psi phi =
      cmp116SourcePi4FullComplexR2Matrix
        (R := R) anchor K hc hmass hK
          (cmp116SourceRestrictedShiftedCoupling contourCarrier e z) :=
  rfl

@[simp]
theorem withSourcePi4RestrictedComplexGaussian_r3Matrix
    {nDelta nY M Q Nc R : ℕ}
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
    (z : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    (C.withSourcePi4RestrictedComplexGaussian
      anchor contourCarrier hcarrier e Z0 K root
      hsourceRange hrange hc hmass hK hD hcontour).r3Matrix
        z tau psi phi =
      cmp116SourcePi4FullComplexR3Matrix
        (R := R) anchor K root hc hmass hK Z0
          (cmp116SourceRestrictedShiftedCoupling contourCarrier e z) :=
  rfl

/-- Every use of the restricted constructor carries the intended physical
gap-contour cardinality identity. -/
theorem withSourcePi4RestrictedComplexGaussian_delta_card
    {nDelta : ℕ} {Δ : Type*} [DecidableEq Δ]
    (contourCarrier : Finset Δ)
    (e : Fin nDelta ≃ ↥contourCarrier) :
    nDelta = contourCarrier.card :=
  cmp116SourceRestrictedShiftedCoupling_card contourCarrier e

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
