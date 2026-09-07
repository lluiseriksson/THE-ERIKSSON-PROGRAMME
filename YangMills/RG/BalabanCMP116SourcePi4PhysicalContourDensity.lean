/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4ShiftedComplexContour
import YangMills.RG.BalabanCMP116Eq214LogDeterminantDensity
import YangMills.RG.BalabanCMP116SourcePi4PhysicalComplexContourNonsingularity

/-!
# Install the literal source `Pi^4` complex Gaussian in equation (2.14)

This module is the source-to-ledger dictionary for the Gaussian part of
CMP116.  It replaces every abstract Gaussian field of
`CMP116Eq214PhysicalContourDensity` by the complete source construction:

* the fixed real physical covariance root;
* the exact fully-coupled covariance, precision, and Gamma;
* the complete complex weakened covariance and its inverse;
* the literal complex Gamma with the physical complement projection;
* the logarithmic determinant branch.

The zero-based Cauchy coordinate is translated to the source coupling by
`sigma_source = 1 + sigma`.  Consequently the generic corrections `R1`,
`R2`, and `R3` are definitionally the literal source corrections already
constructed.  The only analytic input retained by the constructor is
nonsingularity of the *actual* complete source covariance on the traversed
polydisc; the physical producer for that statement is supplied by
`BalabanCMP116SourcePi4PhysicalComplexContourNonsingularity`.
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

/-- Install the complete source-specific complex Gaussian data while
preserving the already installed potential and cutoff fields. -/
def withSourcePi4FullComplexGaussian
    {nDelta nY M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    {Site E : Type*} {Psi Phi : Site → Type*} [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond 4 (M * (2 * Q))) Site Psi Phi E (Nc ^ 2 - 1))
    (e : Fin nDelta ≃ FinBox 4 (2 * Q))
    (anchor : FinBox 4 Q)
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
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (hcontour : ∀ z,
      CMP116Eq214ShiftedPolydisc nDelta C.deltaRadius z →
      (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
        (R := R) anchor K hc hmass hK
          (cmp116SourcePi4ShiftedCoupling e z)).det ≠ 0) :
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
        (cmp116SourcePi4ShiftedCoupling e z)
  baseCovariance := fun _ _ =>
    cmp116SourcePi4PhysicalBaseCovarianceMatrix K hc hmass hK
  contourCovariance := fun z _ _ _ =>
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
      (R := R) anchor K hc hmass hK
        (cmp116SourcePi4ShiftedCoupling e z)
  basePrecision := fun _ _ =>
    cmp116PhysicalEndomorphismComplexMatrix K
  contourPrecision := fun z _ _ _ =>
    cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
      (R := R) anchor K hc hmass hK
        (cmp116SourcePi4ShiftedCoupling e z)
  determinantDensity := fun z _ _ _ =>
    cmp116Eq214LogDeterminantDensity
      (cmp116PhysicalEndomorphismComplexMatrix K)
      (cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
        (R := R) anchor K hc hmass hK
          (cmp116SourcePi4ShiftedCoupling e z))
  potential := C.potential
  bondField := C.bondField
  threshold := C.threshold
  contourGamma_zero := by
    intro psi phi
    rw [cmp116SourcePi4ShiftedCoupling_zero]
    exact cmp116SourcePi4FullComplexGammaMatrix_one_eq_physical
      anchor K root hsourceRange hrange hc hmass hK hD Z0
  contourCovariance_zero := by
    intro psi phi
    rw [cmp116SourcePi4ShiftedCoupling_zero]
    exact cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_one_eq_exact
      anchor K hsourceRange hrange hc hmass hK hD
  contourPrecision_zero := by
    intro psi phi
    rw [cmp116SourcePi4ShiftedCoupling_zero]
    exact cmp116SourcePi4FullComplexWeakenedPrecisionMatrix_one_eq_physical
      anchor K hsourceRange hrange hc hmass hK hD
  determinantDensity_zero := by
    intro psi phi
    rw [cmp116SourcePi4ShiftedCoupling_zero]
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
            (cmp116SourcePi4ShiftedCoupling e z)).det ≠ 0 := by
      unfold cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
      exact isUnit_iff_ne_zero.mp
        (Matrix.isUnit_nonsing_inv_det
          (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
            (R := R) anchor K hc hmass hK
              (cmp116SourcePi4ShiftedCoupling e z))
          (isUnit_iff_ne_zero.mpr (hcontour z hz)))
    exact cmp116Eq214LogDeterminantDensity_sq_mul_base_det
      (cmp116PhysicalEndomorphismComplexMatrix K)
      (cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
        (R := R) anchor K hc hmass hK
          (cmp116SourcePi4ShiftedCoupling e z))
      hbasePrecision hcontourPrecision
  potential_zero := C.potential_zero

/-- Source-facing constructor with contour nonsingularity generated from the
literal complex patched-walk bound and one scalar Neumann inequality.

`radius` bounds the displacement from full coupling.  Since the Cauchy
coordinate itself lies in `‖z_i‖ ≤ 1 + deltaRadius i`, the only dictionary
condition is `1 + deltaRadius i ≤ radius`.  The source coupling is then
automatically bounded by `1 + radius`. -/
def withSourcePi4FullComplexGaussianOfPhysicalContour
    {nDelta nY M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    {Site E : Type*} {Psi Phi : Site → Type*} [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond 4 (M * (2 * Q))) Site Psi Phi E (Nc ^ 2 - 1))
    (e : Fin nDelta ≃ FinBox 4 (2 * Q))
    (anchor : FinBox 4 Q)
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
    (Z0 : Finset (FinBox 4 (2 * Q)))
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
  apply C.withSourcePi4FullComplexGaussian e anchor K root
    hsourceRange hfiniteRange hc hmass hK hD Z0
  intro z hz
  apply
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_det_ne_zero_of_physicalContour
      (radius := radius) (Rweak := 1 + radius)
      anchor K hsourceRange hfiniteRange hc hmass hK hD
      hAhead hrho hrate hgeom Cert htri hΔ hΔ1
      (cmp116SourcePi4ShiftedCoupling e z)
      hradius
      (by linarith)
  · intro d
    exact
      (norm_cmp116SourcePi4ShiftedCoupling_sub_one_le
        e C.deltaRadius z hz d).trans (hradiusCap (e.symm d))
  · intro d
    calc
      ‖cmp116SourcePi4ShiftedCoupling e z d‖
          ≤ 2 + C.deltaRadius (e.symm d) :=
        norm_cmp116SourcePi4ShiftedCoupling_le
          e C.deltaRadius z hz d
      _ = 1 + (1 + C.deltaRadius (e.symm d)) := by ring
      _ ≤ 1 + radius := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left (hradiusCap (e.symm d)) 1
  · exact hseries
  · exact hneumann

@[simp]
theorem withSourcePi4FullComplexGaussian_r1Matrix
    {nDelta nY M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    {Site E : Type*} {Psi Phi : Site → Type*} [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond 4 (M * (2 * Q))) Site Psi Phi E (Nc ^ 2 - 1))
    (e : Fin nDelta ≃ FinBox 4 (2 * Q))
    (anchor : FinBox 4 Q) (K root : PhysicalEndomorphism M Q Nc)
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
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (hcontour : ∀ z,
      CMP116Eq214ShiftedPolydisc nDelta C.deltaRadius z →
      (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
        (R := R) anchor K hc hmass hK
          (cmp116SourcePi4ShiftedCoupling e z)).det ≠ 0)
    (z : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    (C.withSourcePi4FullComplexGaussian e anchor K root
      hsourceRange hrange hc hmass hK hD Z0 hcontour).r1Matrix
        z tau psi phi =
      cmp116SourcePi4FullComplexR1Matrix
        (R := R) anchor K root hc hmass hK Z0
          (cmp116SourcePi4ShiftedCoupling e z) :=
  rfl

@[simp]
theorem withSourcePi4FullComplexGaussian_r2Matrix
    {nDelta nY M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    {Site E : Type*} {Psi Phi : Site → Type*} [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond 4 (M * (2 * Q))) Site Psi Phi E (Nc ^ 2 - 1))
    (e : Fin nDelta ≃ FinBox 4 (2 * Q))
    (anchor : FinBox 4 Q) (K root : PhysicalEndomorphism M Q Nc)
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
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (hcontour : ∀ z,
      CMP116Eq214ShiftedPolydisc nDelta C.deltaRadius z →
      (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
        (R := R) anchor K hc hmass hK
          (cmp116SourcePi4ShiftedCoupling e z)).det ≠ 0)
    (z : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    (C.withSourcePi4FullComplexGaussian e anchor K root
      hsourceRange hrange hc hmass hK hD Z0 hcontour).r2Matrix
        z tau psi phi =
      cmp116SourcePi4FullComplexR2Matrix
        (R := R) anchor K hc hmass hK
          (cmp116SourcePi4ShiftedCoupling e z) :=
  rfl

@[simp]
theorem withSourcePi4FullComplexGaussian_r3Matrix
    {nDelta nY M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    {Site E : Type*} {Psi Phi : Site → Type*} [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond 4 (M * (2 * Q))) Site Psi Phi E (Nc ^ 2 - 1))
    (e : Fin nDelta ≃ FinBox 4 (2 * Q))
    (anchor : FinBox 4 Q) (K root : PhysicalEndomorphism M Q Nc)
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
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (hcontour : ∀ z,
      CMP116Eq214ShiftedPolydisc nDelta C.deltaRadius z →
      (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
        (R := R) anchor K hc hmass hK
          (cmp116SourcePi4ShiftedCoupling e z)).det ≠ 0)
    (z : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    (C.withSourcePi4FullComplexGaussian e anchor K root
      hsourceRange hrange hc hmass hK hD Z0 hcontour).r3Matrix
        z tau psi phi =
      cmp116SourcePi4FullComplexR3Matrix
        (R := R) anchor K root hc hmass hK Z0
          (cmp116SourcePi4ShiftedCoupling e z) :=
  rfl

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
