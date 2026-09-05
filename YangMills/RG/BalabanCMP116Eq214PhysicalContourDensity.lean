/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214LocalFiniteGaussianData
import YangMills.RG.BalabanCMP116Eq214CauchyPolydisc

/-!
# CMP116 equation (2.14): complex density over a real reference Gaussian

For complex Cauchy parameters the second law in CMP116 is not a positive
measure.  The source argument compares it with the positive Gaussian at the
real base point and places the contour deformation in a complex density.

This module implements that distinction at the type level.  The covariance
root is one fixed real matrix.  The contour-dependent source, covariance and
precision matrices are complex, and the three corrections are defined
literally by

`R₁ = Γ₁ᵀ C₁ Γ₁ - Γ₀ᵀ C₀ Γ₀`,
`R₂ = K₀ - K₁`, and `R₃ = Γ₁ - Γ₀`.

The terminal identity reconstructs the complete density exactly.  It is an
algebraic source dictionary: it proves no contour bounds, determinant bounds,
holomorphy, or equation-(2.26) estimate.
-/

namespace YangMills.RG

open Matrix
open scoped BigOperators

noncomputable section

/-- Real Gaussian coordinates embedded in the complex coordinate space. -/
def cmp116Eq214ComplexCoordinate
    {ι : Type*} (x : ι → ℝ) : ι → ℂ :=
  fun i => (x i : ℂ)

/-- Analytic bilinear quadratic form.  This deliberately uses transpose and
no complex conjugation. -/
def cmp116Eq214ComplexQuadratic
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (x : ι → ℝ) : ℂ :=
  (1 / 2 : ℂ) *
    (cmp116Eq214ComplexCoordinate x ⬝ᵥ
      (A *ᵥ cmp116Eq214ComplexCoordinate x))

/-- Analytic mixed form with the CMP116 ordering `B · R₃ X`. -/
def cmp116Eq214ComplexMixed
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (x b : ι → ℝ) : ℂ :=
  cmp116Eq214ComplexCoordinate b ⬝ᵥ
    (A *ᵥ cmp116Eq214ComplexCoordinate x)

/-- Source-faithful complex-contour data.  The real reference root is fixed,
whereas all contour dependence is carried by an explicit complex density.
The base-point fields certify that this density is normalized to one when the
contour parameters vanish. -/
structure CMP116Eq214PhysicalContourDensity
    (nDelta nY : ℕ) (Bond Site : Type*) (Psi Phi : Site → Type*)
    (E : Type*) [Fintype Bond] [DecidableEq Bond] [Norm E] (lieDim : ℕ) where
  spectatorSupport : Finset Site
  fluctuationSupport : Finset Site
  deltaRadius : Fin nDelta → ℝ
  yRadius : Fin nY → ℝ
  referenceRoot :
    Matrix (Bond × Fin lieDim) (Bond × Fin lieDim) ℝ
  baseGamma :
    RestrictedField spectatorSupport Psi →
      RestrictedField fluctuationSupport Phi →
        Matrix (Bond × Fin lieDim) (Bond × Fin lieDim) ℂ
  contourGamma :
    (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      RestrictedField spectatorSupport Psi →
      RestrictedField fluctuationSupport Phi →
        Matrix (Bond × Fin lieDim) (Bond × Fin lieDim) ℂ
  baseCovariance :
    RestrictedField spectatorSupport Psi →
      RestrictedField fluctuationSupport Phi →
        Matrix (Bond × Fin lieDim) (Bond × Fin lieDim) ℂ
  contourCovariance :
    (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      RestrictedField spectatorSupport Psi →
      RestrictedField fluctuationSupport Phi →
        Matrix (Bond × Fin lieDim) (Bond × Fin lieDim) ℂ
  basePrecision :
    RestrictedField spectatorSupport Psi →
      RestrictedField fluctuationSupport Phi →
        Matrix (Bond × Fin lieDim) (Bond × Fin lieDim) ℂ
  contourPrecision :
    (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      RestrictedField spectatorSupport Psi →
      RestrictedField fluctuationSupport Phi →
        Matrix (Bond × Fin lieDim) (Bond × Fin lieDim) ℂ
  determinantDensity :
    (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      RestrictedField spectatorSupport Psi →
      RestrictedField fluctuationSupport Phi → ℂ
  potential :
    (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      RestrictedField spectatorSupport Psi →
      RestrictedField fluctuationSupport Phi →
      CMP116Eq214GaussianCoordinate Bond lieDim → ℂ
  bondField : CMP116Eq214GaussianCoordinate Bond lieDim → Bond → E
  threshold : ℝ
  contourGamma_zero : ∀ psi phi,
    contourGamma 0 0 psi phi = baseGamma psi phi
  contourCovariance_zero : ∀ psi phi,
    contourCovariance 0 0 psi phi = baseCovariance psi phi
  contourPrecision_zero : ∀ psi phi,
    contourPrecision 0 0 psi phi = basePrecision psi phi
  determinantDensity_zero : ∀ psi phi,
    determinantDensity 0 0 psi phi = 1
  determinantDensity_sq_mul_basePrecision_det : ∀ sigma tau psi phi,
    CMP116Eq214ShiftedPolydisc nDelta deltaRadius sigma →
    CMP116Eq214ShiftedPolydisc nY yRadius tau →
    determinantDensity sigma tau psi phi ^ 2 *
        (basePrecision psi phi).det =
      (contourPrecision sigma tau psi phi).det
  potential_zero : ∀ psi phi b,
    potential 0 0 psi phi b = 0

namespace CMP116Eq214PhysicalContourDensity

variable {nDelta nY lieDim : ℕ} {Bond Site E : Type*}
  {Psi Phi : Site → Type*} [Fintype Bond] [DecidableEq Bond] [Norm E]

private abbrev Coord (Bond : Type*) (lieDim : ℕ) :=
  Bond × Fin lieDim

/-- Literal complex `R₁`, with the analytic transpose rather than a Hermitian
adjoint. -/
def r1Matrix
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    Matrix (Coord Bond lieDim) (Coord Bond lieDim) ℂ :=
  (C.contourGamma sigma tau psi phi)ᵀ *
      C.contourCovariance sigma tau psi phi *
      C.contourGamma sigma tau psi phi -
    (C.baseGamma psi phi)ᵀ * C.baseCovariance psi phi * C.baseGamma psi phi

/-- Literal complex `R₂ = K₀ - K₁`, with the source-prescribed sign. -/
def r2Matrix
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    Matrix (Coord Bond lieDim) (Coord Bond lieDim) ℂ :=
  C.basePrecision psi phi - C.contourPrecision sigma tau psi phi

/-- Literal complex `R₃ = Γ₁ - Γ₀`. -/
def r3Matrix
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    Matrix (Coord Bond lieDim) (Coord Bond lieDim) ℂ :=
  C.contourGamma sigma tau psi phi - C.baseGamma psi phi

/-- Quotient-of-determinants form of the normalization identity.  The
division is exposed only after the base precision determinant is certified
nonzero. -/
theorem determinantDensity_sq_eq_det_div
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (hsigma : CMP116Eq214ShiftedPolydisc nDelta C.deltaRadius sigma)
    (htau : CMP116Eq214ShiftedPolydisc nY C.yRadius tau)
    (hbase : (C.basePrecision psi phi).det ≠ 0) :
    C.determinantDensity sigma tau psi phi ^ 2 =
      (C.contourPrecision sigma tau psi phi).det /
        (C.basePrecision psi phi).det := by
  exact (eq_div_iff hbase).2
    (C.determinantDensity_sq_mul_basePrecision_det
      sigma tau psi phi hsigma htau)

/-- Complete contour correction exponent relative to the real base Gaussian. -/
def correctionExponent
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (x b : CMP116Eq214GaussianCoordinate Bond lieDim) : ℂ :=
  cmp116Eq214ComplexQuadratic (C.r1Matrix sigma tau psi phi) x +
    cmp116Eq214ComplexQuadratic (C.r2Matrix sigma tau psi phi) b -
    cmp116Eq214ComplexMixed (C.r3Matrix sigma tau psi phi) x b +
    C.potential sigma tau psi phi b

/-- Install the complex density in the existing local finite-Gaussian object.
The conditioned measure remains the fixed positive reference Gaussian. -/
def toLocalFiniteGaussianData
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim) :
    CMP116Eq214LocalFiniteGaussianData nDelta nY
      Bond Site Psi Phi E lieDim where
  spectatorSupport := C.spectatorSupport
  fluctuationSupport := C.fluctuationSupport
  deltaRadius := C.deltaRadius
  yRadius := C.yRadius
  covarianceRoot := fun _ _ => C.referenceRoot
  outerWeight := fun sigma tau psi phi x =>
    C.determinantDensity sigma tau psi phi *
      Complex.exp
        (cmp116Eq214ComplexQuadratic (C.r1Matrix sigma tau psi phi) x)
  innerWeight := fun sigma tau psi phi x b =>
    Complex.exp
      (-cmp116Eq214ComplexMixed (C.r3Matrix sigma tau psi phi) x b)
  bondField := C.bondField
  threshold := C.threshold
  interactionExponent := fun sigma tau psi phi b =>
    cmp116Eq214ComplexQuadratic (C.r2Matrix sigma tau psi phi) b +
      C.potential sigma tau psi phi b

/-- The contour parameters cannot deform the positive reference measure: they
occur only in the explicit complex density. -/
@[simp] theorem conditionedMeasure_eq_reference
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ) :
    C.toLocalFiniteGaussianData.toLocalAnalyticData.conditionedMeasure
        sigma tau =
      matrixGaussianPi C.referenceRoot := by
  rfl

/-- Exact density factorization.  No norm or analyticity hypothesis is used. -/
theorem weightProduct_eq_determinantDensity_mul_exp_correctionExponent
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (x b : CMP116Eq214GaussianCoordinate Bond lieDim) :
    let G := C.toLocalFiniteGaussianData
    G.outerWeight sigma tau psi phi x *
        G.innerWeight sigma tau psi phi x b *
        Complex.exp (G.interactionExponent sigma tau psi phi b) =
      C.determinantDensity sigma tau psi phi *
        Complex.exp (C.correctionExponent sigma tau psi phi x b) := by
  dsimp [toLocalFiniteGaussianData]
  calc
    (C.determinantDensity sigma tau psi phi *
          Complex.exp
            (cmp116Eq214ComplexQuadratic
              (C.r1Matrix sigma tau psi phi) x)) *
        Complex.exp
          (-cmp116Eq214ComplexMixed
            (C.r3Matrix sigma tau psi phi) x b) *
        Complex.exp
          (cmp116Eq214ComplexQuadratic
              (C.r2Matrix sigma tau psi phi) b +
            C.potential sigma tau psi phi b) =
      C.determinantDensity sigma tau psi phi *
        (Complex.exp
            (cmp116Eq214ComplexQuadratic
              (C.r1Matrix sigma tau psi phi) x) *
          Complex.exp
            (-cmp116Eq214ComplexMixed
              (C.r3Matrix sigma tau psi phi) x b) *
          Complex.exp
            (cmp116Eq214ComplexQuadratic
                (C.r2Matrix sigma tau psi phi) b +
              C.potential sigma tau psi phi b)) := by ring
    _ = C.determinantDensity sigma tau psi phi *
        Complex.exp
          (cmp116Eq214ComplexQuadratic
              (C.r1Matrix sigma tau psi phi) x +
            -cmp116Eq214ComplexMixed
              (C.r3Matrix sigma tau psi phi) x b +
            (cmp116Eq214ComplexQuadratic
              (C.r2Matrix sigma tau psi phi) b +
              C.potential sigma tau psi phi b)) := by
      simp only [Complex.exp_add]
    _ = C.determinantDensity sigma tau psi phi *
        Complex.exp (C.correctionExponent sigma tau psi phi x b) := by
      congr 2
      simp only [correctionExponent]
      ring

/-- Exact norm of the contour density.  Every future domination theorem must
therefore control the real part of the literal correction exponent, not a
separate synthetic majorant. -/
theorem norm_weightProduct_eq
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (x b : CMP116Eq214GaussianCoordinate Bond lieDim) :
    let G := C.toLocalFiniteGaussianData
    ‖G.outerWeight sigma tau psi phi x *
        G.innerWeight sigma tau psi phi x b *
        Complex.exp (G.interactionExponent sigma tau psi phi b)‖ =
      ‖C.determinantDensity sigma tau psi phi‖ *
        Real.exp ((C.correctionExponent sigma tau psi phi x b).re) := by
  dsimp only
  rw [C.weightProduct_eq_determinantDensity_mul_exp_correctionExponent,
    norm_mul, Complex.norm_exp]

/-- The same exact reduction for the outer factor alone. -/
theorem norm_outerWeight_eq
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (x : CMP116Eq214GaussianCoordinate Bond lieDim) :
    ‖C.toLocalFiniteGaussianData.outerWeight sigma tau psi phi x‖ =
      ‖C.determinantDensity sigma tau psi phi‖ *
        Real.exp
          ((cmp116Eq214ComplexQuadratic
            (C.r1Matrix sigma tau psi phi) x).re) := by
  simp [toLocalFiniteGaussianData, Complex.norm_exp]

/-- The determinant normalization and the localized real part of `R₁`
produce the energy-dependent outer bound used by equation (2.26).

This theorem deliberately leaves the two source estimates separate: it does
not store a complete term bound or manufacture a post-hoc polymer weight. -/
theorem norm_outerWeight_le_of_determinantDensity_of_r1
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (S : Finset (Bond × Fin lieDim))
    (outerBound outerRate : ℝ)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (x : CMP116Eq214GaussianCoordinate Bond lieDim)
    (hdet :
      ‖C.determinantDensity sigma tau psi phi‖ ≤ outerBound)
    (hr1 :
      (cmp116Eq214ComplexQuadratic
        (C.r1Matrix sigma tau psi phi) x).re ≤
          outerRate * ∑ i ∈ S, x i ^ 2) :
    ‖C.toLocalFiniteGaussianData.outerWeight sigma tau psi phi x‖ ≤
      outerBound * Real.exp (outerRate * ∑ i ∈ S, x i ^ 2) := by
  rw [C.norm_outerWeight_eq]
  exact mul_le_mul
    hdet
    (Real.exp_le_exp.mpr hr1)
    (Real.exp_pos _).le
    ((norm_nonneg _).trans hdet)

/-- All three correction matrices vanish at the real base point. -/
@[simp] theorem r1Matrix_zero
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    C.r1Matrix 0 0 psi phi = 0 := by
  simp [r1Matrix, C.contourGamma_zero, C.contourCovariance_zero]

@[simp] theorem r2Matrix_zero
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    C.r2Matrix 0 0 psi phi = 0 := by
  simp [r2Matrix, C.contourPrecision_zero]

@[simp] theorem r3Matrix_zero
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    C.r3Matrix 0 0 psi phi = 0 := by
  simp [r3Matrix, C.contourGamma_zero]

/-- The complex density is exactly normalized at the real base point. -/
theorem weightProduct_zero_eq_one
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (x b : CMP116Eq214GaussianCoordinate Bond lieDim) :
    let G := C.toLocalFiniteGaussianData
    G.outerWeight 0 0 psi phi x * G.innerWeight 0 0 psi phi x b *
        Complex.exp (G.interactionExponent 0 0 psi phi b) = 1 := by
  have h := C.weightProduct_eq_determinantDensity_mul_exp_correctionExponent
    (sigma := (0 : Fin nDelta → ℂ)) (tau := (0 : Fin nY → ℂ))
    psi phi x b
  simpa [correctionExponent, C.determinantDensity_zero, C.potential_zero,
    cmp116Eq214ComplexQuadratic, cmp116Eq214ComplexMixed] using h

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
