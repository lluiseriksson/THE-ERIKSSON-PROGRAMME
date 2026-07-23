/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4PhysicalContourDensity
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Reindex the literal source contour into CMP116 ledger coordinates

The complete source walk is naturally indexed by physical bonds and Lie
coordinates.  The equation-(2.26) ledger is indexed by CMP116 cubes and
scalar coordinates.  `PhysicalGaugeCMP116Dictionary.coordEquiv` is the
certified finite equivalence between precisely these two coordinate types.

This module transports the literal source covariance, precision, root, and
Gamma through that equivalence.  The same equivalence is used on rows and
columns, so matrix multiplication, analytic transpose, and determinant are
preserved exactly.  The potential and cutoff fields already installed in the
ledger object are left untouched.
-/

namespace YangMills.RG

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- Reindex a physical bond--Lie matrix into the scalar CMP116 coordinates
of the certified dictionary. -/
def cmp116ReindexPhysicalMatrix
    {M Q Nc L lieDim : ℕ}
    [NeZero M] [NeZero Q] [NeZero L]
    (Dict : PhysicalGaugeCMP116Dictionary
      4 (M * (2 * Q)) Nc 4 L lieDim)
    {𝕜 : Type*}
    (A : Matrix
      (PhysicalGaugeCoordIndex 4 (M * (2 * Q)) Nc)
      (PhysicalGaugeCoordIndex 4 (M * (2 * Q)) Nc) 𝕜) :
    Matrix (CMP116CoordIndex 4 L lieDim)
      (CMP116CoordIndex 4 L lieDim) 𝕜 :=
  Matrix.reindex Dict.coordEquiv.symm Dict.coordEquiv.symm A

@[simp]
theorem det_cmp116ReindexPhysicalMatrix
    {M Q Nc L lieDim : ℕ}
    [NeZero M] [NeZero Q] [NeZero L]
    (Dict : PhysicalGaugeCMP116Dictionary
      4 (M * (2 * Q)) Nc 4 L lieDim)
    (A : Matrix
      (PhysicalGaugeCoordIndex 4 (M * (2 * Q)) Nc)
      (PhysicalGaugeCoordIndex 4 (M * (2 * Q)) Nc) ℂ) :
    (cmp116ReindexPhysicalMatrix Dict A).det = A.det := by
  exact Matrix.det_reindex_self Dict.coordEquiv.symm A

/-- Reindexing preserves the analytic covariance sandwich used by `R1`.
The transpose is purely algebraic; no conjugation is introduced. -/
theorem cmp116ReindexPhysicalMatrix_covarianceSandwichSub
    {M Q Nc L lieDim : ℕ}
    [NeZero M] [NeZero Q] [NeZero L]
    (Dict : PhysicalGaugeCMP116Dictionary
      4 (M * (2 * Q)) Nc 4 L lieDim)
    (G0 G1 C0 C1 : Matrix
      (PhysicalGaugeCoordIndex 4 (M * (2 * Q)) Nc)
      (PhysicalGaugeCoordIndex 4 (M * (2 * Q)) Nc) ℂ) :
    cmp116ReindexPhysicalMatrix Dict
        (Matrix.transpose G1 * C1 * G1 -
          Matrix.transpose G0 * C0 * G0) =
      Matrix.transpose (cmp116ReindexPhysicalMatrix Dict G1) *
          cmp116ReindexPhysicalMatrix Dict C1 *
          cmp116ReindexPhysicalMatrix Dict G1 -
        Matrix.transpose (cmp116ReindexPhysicalMatrix Dict G0) *
          cmp116ReindexPhysicalMatrix Dict C0 *
          cmp116ReindexPhysicalMatrix Dict G0 := by
  change
    Matrix.reindexAlgEquiv ℂ ℂ Dict.coordEquiv.symm
        (Matrix.transpose G1 * C1 * G1 -
          Matrix.transpose G0 * C0 * G0) =
      Matrix.transpose
          (Matrix.reindexAlgEquiv ℂ ℂ Dict.coordEquiv.symm G1) *
          Matrix.reindexAlgEquiv ℂ ℂ Dict.coordEquiv.symm C1 *
          Matrix.reindexAlgEquiv ℂ ℂ Dict.coordEquiv.symm G1 -
        Matrix.transpose
          (Matrix.reindexAlgEquiv ℂ ℂ Dict.coordEquiv.symm G0) *
          Matrix.reindexAlgEquiv ℂ ℂ Dict.coordEquiv.symm C0 *
          Matrix.reindexAlgEquiv ℂ ℂ Dict.coordEquiv.symm G0
  simp only [map_sub, map_mul, Matrix.reindexAlgEquiv_apply,
    Matrix.transpose_reindex]

namespace CMP116Eq214PhysicalContourDensity

/-- Install the literal source Gaussian matrices in the CMP116 ledger
coordinate system. -/
def withReindexedSourcePi4FullComplexGaussian
    {nDelta nY M Q Nc R L lieDim : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero L] [NeZero lieDim]
    {Site E : Type*} {Psi Phi : Site → Type*} [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (Cube 4 L) Site Psi Phi E lieDim)
    (Dict : PhysicalGaugeCMP116Dictionary
      4 (M * (2 * Q)) Nc 4 L lieDim)
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
      (Cube 4 L) Site Psi Phi E lieDim where
  spectatorSupport := C.spectatorSupport
  fluctuationSupport := C.fluctuationSupport
  deltaRadius := C.deltaRadius
  yRadius := C.yRadius
  referenceRoot :=
    cmp116ReindexPhysicalMatrix Dict
      (cmp116PhysicalEndomorphismRealMatrix root)
  baseGamma := fun _ _ =>
    cmp116ReindexPhysicalMatrix Dict
      (cmp116SourcePi4PhysicalBaseGammaMatrix K root Z0)
  contourGamma := fun z _ _ _ =>
    cmp116ReindexPhysicalMatrix Dict
      (cmp116SourcePi4FullComplexGammaMatrix
        (R := R) anchor K root hc hmass hK Z0
          (cmp116SourcePi4ShiftedCoupling e z))
  baseCovariance := fun _ _ =>
    cmp116ReindexPhysicalMatrix Dict
      (cmp116SourcePi4PhysicalBaseCovarianceMatrix K hc hmass hK)
  contourCovariance := fun z _ _ _ =>
    cmp116ReindexPhysicalMatrix Dict
      (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
        (R := R) anchor K hc hmass hK
          (cmp116SourcePi4ShiftedCoupling e z))
  basePrecision := fun _ _ =>
    cmp116ReindexPhysicalMatrix Dict
      (cmp116PhysicalEndomorphismComplexMatrix K)
  contourPrecision := fun z _ _ _ =>
    cmp116ReindexPhysicalMatrix Dict
      (cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
        (R := R) anchor K hc hmass hK
          (cmp116SourcePi4ShiftedCoupling e z))
  determinantDensity := fun z _ _ _ =>
    cmp116Eq214LogDeterminantDensity
      (cmp116ReindexPhysicalMatrix Dict
        (cmp116PhysicalEndomorphismComplexMatrix K))
      (cmp116ReindexPhysicalMatrix Dict
        (cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
          (R := R) anchor K hc hmass hK
            (cmp116SourcePi4ShiftedCoupling e z)))
  potential := C.potential
  bondField := C.bondField
  threshold := C.threshold
  contourGamma_zero := by
    intro psi phi
    rw [cmp116SourcePi4ShiftedCoupling_zero,
      cmp116SourcePi4FullComplexGammaMatrix_one_eq_physical
        anchor K root hsourceRange hrange hc hmass hK hD Z0]
  contourCovariance_zero := by
    intro psi phi
    rw [cmp116SourcePi4ShiftedCoupling_zero,
      cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_one_eq_exact
        anchor K hsourceRange hrange hc hmass hK hD]
    rfl
  contourPrecision_zero := by
    intro psi phi
    rw [cmp116SourcePi4ShiftedCoupling_zero,
      cmp116SourcePi4FullComplexWeakenedPrecisionMatrix_one_eq_physical
        anchor K hsourceRange hrange hc hmass hK hD]
  determinantDensity_zero := by
    intro psi phi
    rw [cmp116SourcePi4ShiftedCoupling_zero,
      cmp116SourcePi4FullComplexWeakenedPrecisionMatrix_one_eq_physical
        anchor K hsourceRange hrange hc hmass hK hD]
    exact cmp116Eq214LogDeterminantDensity_self
      (cmp116ReindexPhysicalMatrix Dict
        (cmp116PhysicalEndomorphismComplexMatrix K))
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
    apply cmp116Eq214LogDeterminantDensity_sq_mul_base_det
    · simpa using hbasePrecision
    · simpa using hcontourPrecision
  potential_zero := C.potential_zero

/-- Ledger-coordinate constructor with source contour nonsingularity derived
from the physical patched-walk certificate and the explicit Neumann budget. -/
def withReindexedSourcePi4FullComplexGaussianOfPhysicalContour
    {nDelta nY M Q Nc R Δ L lieDim : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero L] [NeZero lieDim]
    {Site E : Type*} {Psi Phi : Site → Type*} [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (Cube 4 L) Site Psi Phi E lieDim)
    (Dict : PhysicalGaugeCMP116Dictionary
      4 (M * (2 * Q)) Nc 4 L lieDim)
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
      (Cube 4 L) Site Psi Phi E lieDim := by
  apply C.withReindexedSourcePi4FullComplexGaussian Dict e anchor K root
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
theorem withReindexedSourcePi4FullComplexGaussian_r1Matrix
    {nDelta nY M Q Nc R L lieDim : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero L] [NeZero lieDim]
    {Site E : Type*} {Psi Phi : Site → Type*} [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (Cube 4 L) Site Psi Phi E lieDim)
    (Dict : PhysicalGaugeCMP116Dictionary
      4 (M * (2 * Q)) Nc 4 L lieDim)
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
    (C.withReindexedSourcePi4FullComplexGaussian Dict e anchor K root
      hsourceRange hrange hc hmass hK hD Z0 hcontour).r1Matrix
        z tau psi phi =
      cmp116ReindexPhysicalMatrix Dict
        (cmp116SourcePi4FullComplexR1Matrix
          (R := R) anchor K root hc hmass hK Z0
            (cmp116SourcePi4ShiftedCoupling e z)) := by
  unfold r1Matrix cmp116SourcePi4FullComplexR1Matrix
  exact
    (cmp116ReindexPhysicalMatrix_covarianceSandwichSub Dict
      (cmp116SourcePi4PhysicalBaseGammaMatrix K root Z0)
      (cmp116SourcePi4FullComplexGammaMatrix
        (R := R) anchor K root hc hmass hK Z0
          (cmp116SourcePi4ShiftedCoupling e z))
      (cmp116SourcePi4PhysicalBaseCovarianceMatrix K hc hmass hK)
      (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
        (R := R) anchor K hc hmass hK
          (cmp116SourcePi4ShiftedCoupling e z))).symm

@[simp]
theorem withReindexedSourcePi4FullComplexGaussian_r2Matrix
    {nDelta nY M Q Nc R L lieDim : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero L] [NeZero lieDim]
    {Site E : Type*} {Psi Phi : Site → Type*} [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (Cube 4 L) Site Psi Phi E lieDim)
    (Dict : PhysicalGaugeCMP116Dictionary
      4 (M * (2 * Q)) Nc 4 L lieDim)
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
    (C.withReindexedSourcePi4FullComplexGaussian Dict e anchor K root
      hsourceRange hrange hc hmass hK hD Z0 hcontour).r2Matrix
        z tau psi phi =
      cmp116ReindexPhysicalMatrix Dict
        (cmp116SourcePi4FullComplexR2Matrix
          (R := R) anchor K hc hmass hK
            (cmp116SourcePi4ShiftedCoupling e z)) := by
  rfl

@[simp]
theorem withReindexedSourcePi4FullComplexGaussian_r3Matrix
    {nDelta nY M Q Nc R L lieDim : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero L] [NeZero lieDim]
    {Site E : Type*} {Psi Phi : Site → Type*} [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (Cube 4 L) Site Psi Phi E lieDim)
    (Dict : PhysicalGaugeCMP116Dictionary
      4 (M * (2 * Q)) Nc 4 L lieDim)
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
    (C.withReindexedSourcePi4FullComplexGaussian Dict e anchor K root
      hsourceRange hrange hc hmass hK hD Z0 hcontour).r3Matrix
        z tau psi phi =
      cmp116ReindexPhysicalMatrix Dict
        (cmp116SourcePi4FullComplexR3Matrix
          (R := R) anchor K root hc hmass hK Z0
            (cmp116SourcePi4ShiftedCoupling e z)) := by
  rfl

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
