/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214PhysicalContourR3Source
import YangMills.RG.BalabanCMP116Eq225LinearSource
import YangMills.RG.BalabanCMP116ComplexSourceSchur

/-!
# The conditioned outer Gaussian carrier in CMP116 equation (2.23)

Balaban's literal source operator `Gamma` is global.  After the random-walk
localization, however, equation (2.23) integrates the outer product Gaussian
as `dmu0(X)|_Z`.  In ambient finite coordinates this means that every
occurrence of the outer variable is evaluated at `P_Z X`.

This module records that restriction at the variable boundary.  It does not
alter the covariance root and it does not insert a projection into the
definition of the source operator.  Algebraically, precomposing `Gamma` by
the coordinate projection makes `R3` equal to `R3 * P_Z` and `R1` equal to
`P_Zᵀ * R1 * P_Z`, so both outer-field terms see the same conditioned
variable.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CMP116Eq214PhysicalContourDensity

variable {nDelta nY lieDim : ℕ} {Bond Site E : Type*}
  {Psi Phi : Site → Type*} [Fintype Bond] [DecidableEq Bond] [Norm E]

private abbrev Coord (Bond : Type*) (lieDim : ℕ) :=
  Bond × Fin lieDim

/-- Complexification of the real diagonal projection onto an outer Gaussian
carrier. -/
def conditionedOuterProjection
    (S : Finset (Coord Bond lieDim)) :
    Matrix (Coord Bond lieDim) (Coord Bond lieDim) ℂ :=
  (cmp116Eq223CoordinateProjection S).map Complex.ofRealHom

@[simp]
theorem conditionedOuterProjection_re
    (S : Finset (Coord Bond lieDim)) (i j : Coord Bond lieDim) :
    (conditionedOuterProjection S i j).re =
      cmp116Eq223CoordinateProjection S i j := by
  rfl

@[simp]
theorem conditionedOuterProjection_im
    (S : Finset (Coord Bond lieDim)) (i j : Coord Bond lieDim) :
    (conditionedOuterProjection S i j).im = 0 := by
  rfl

/-- Precompose the literal source operator by the carrier projection of the
conditioned outer Gaussian variable.  All non-outer data are unchanged. -/
def withConditionedOuterCarrier
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (S : Finset (Coord Bond lieDim)) :
    CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim where
  spectatorSupport := C.spectatorSupport
  fluctuationSupport := C.fluctuationSupport
  deltaRadius := C.deltaRadius
  yRadius := C.yRadius
  referenceRoot := C.referenceRoot
  baseGamma := fun psi phi =>
    C.baseGamma psi phi * conditionedOuterProjection S
  contourGamma := fun sigma tau psi phi =>
    C.contourGamma sigma tau psi phi * conditionedOuterProjection S
  baseCovariance := C.baseCovariance
  contourCovariance := C.contourCovariance
  basePrecision := C.basePrecision
  contourPrecision := C.contourPrecision
  determinantDensity := C.determinantDensity
  potential := C.potential
  bondField := C.bondField
  threshold := C.threshold
  contourGamma_zero := by
    intro psi phi
    rw [C.contourGamma_zero]
  contourCovariance_zero := C.contourCovariance_zero
  contourPrecision_zero := C.contourPrecision_zero
  determinantDensity_zero := C.determinantDensity_zero
  determinantDensity_sq_mul_basePrecision_det :=
    C.determinantDensity_sq_mul_basePrecision_det
  potential_zero := C.potential_zero

@[simp]
theorem withConditionedOuterCarrier_r3Matrix
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (S : Finset (Coord Bond lieDim))
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    (C.withConditionedOuterCarrier S).r3Matrix sigma tau psi phi =
      C.r3Matrix sigma tau psi phi * conditionedOuterProjection S := by
  simp [r3Matrix, withConditionedOuterCarrier, Matrix.sub_mul]

@[simp]
theorem withConditionedOuterCarrier_r2Matrix
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (S : Finset (Coord Bond lieDim))
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    (C.withConditionedOuterCarrier S).r2Matrix sigma tau psi phi =
      C.r2Matrix sigma tau psi phi := by
  rfl

@[simp]
theorem conditionedOuterProjection_transpose
    (S : Finset (Coord Bond lieDim)) :
    (conditionedOuterProjection S).transpose =
      conditionedOuterProjection S := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    simp [conditionedOuterProjection, cmp116Eq223CoordinateProjection,
      Matrix.transpose_apply, Matrix.diagonal]
  · simp [conditionedOuterProjection, cmp116Eq223CoordinateProjection,
      Matrix.transpose_apply, Matrix.diagonal, hij, Ne.symm hij]

/-- Precomposing both Gamma operators by the conditioned outer projection
compresses `R1` on both sides and does not alter its middle covariance. -/
theorem withConditionedOuterCarrier_r1Matrix
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (S : Finset (Coord Bond lieDim))
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    (C.withConditionedOuterCarrier S).r1Matrix sigma tau psi phi =
      (conditionedOuterProjection S).transpose *
        C.r1Matrix sigma tau psi phi *
          conditionedOuterProjection S := by
  simp only [r1Matrix, withConditionedOuterCarrier,
    Matrix.transpose_mul, Matrix.mul_assoc]
  noncomm_ring

theorem realPart_conditionedOuterProjection_mul
    (A : Matrix (Coord Bond lieDim) (Coord Bond lieDim) ℂ)
    (S : Finset (Coord Bond lieDim)) :
    cmp116Eq214RealPartMatrix (A * conditionedOuterProjection S) =
      cmp116Eq214RealPartMatrix A *
        cmp116Eq223CoordinateProjection S := by
  classical
  ext i j
  simp [cmp116Eq214RealPartMatrix, Matrix.mul_apply, Complex.mul_re]

/-- The canonical real `R3` source of the conditioned density is the literal
source evaluated on the projected outer field. -/
theorem withConditionedOuterCarrier_r3RealSource
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (S : Finset (Coord Bond lieDim))
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (x : CMP116Eq214GaussianCoordinate Bond lieDim) :
    (C.withConditionedOuterCarrier S).r3RealSource
        sigma tau psi phi x =
      C.r3RealSource sigma tau psi phi
        ((cmp116Eq223CoordinateProjection S).mulVec x) := by
  simp only [r3RealSource, withConditionedOuterCarrier_r3Matrix,
    realPart_conditionedOuterProjection_mul, Matrix.mulVec_mulVec]

/-- The source energy of the conditioned outer variable is controlled by the
literal `R3` operator norm times the exact carrier energy. -/
theorem dotProduct_conditionedOuterCarrier_r3RealSource_self_le
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (S : Finset (Coord Bond lieDim))
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (x : CMP116Eq214GaussianCoordinate Bond lieDim) :
    (C.withConditionedOuterCarrier S).r3RealSource sigma tau psi phi x ⬝ᵥ
        (C.withConditionedOuterCarrier S).r3RealSource sigma tau psi phi x ≤
      ‖cmp116Eq214RealPartMatrix
          (C.r3Matrix sigma tau psi phi)‖ ^ 2 *
        ∑ i ∈ S, x i ^ 2 := by
  rw [C.withConditionedOuterCarrier_r3RealSource S]
  simpa [r3RealSource, dotProduct] using
    (dotProduct_linearLocalizedSource_le S
      (cmp116Eq214RealPartMatrix (C.r3Matrix sigma tau psi phi)) x)

section

open scoped Matrix.Norms.Operator

/-- Bilateral row/column version of the preceding source-energy bound.  This
is the dimension-free form consumed by the physical `R3` estimates. -/
theorem dotProduct_conditionedOuterCarrier_r3RealSource_self_le_bilateral
    [Nonempty (Coord Bond lieDim)]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (S : Finset (Coord Bond lieDim))
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (x : CMP116Eq214GaussianCoordinate Bond lieDim) :
    (C.withConditionedOuterCarrier S).r3RealSource sigma tau psi phi x ⬝ᵥ
        (C.withConditionedOuterCarrier S).r3RealSource sigma tau psi phi x ≤
      ‖C.r3Matrix sigma tau psi phi‖ *
          ‖(C.r3Matrix sigma tau psi phi).transpose‖ *
        ∑ i ∈ S, x i ^ 2 := by
  rw [C.withConditionedOuterCarrier_r3RealSource S]
  have h :=
    dotProduct_realPart_mulVec_self_le_linfty_bilateral
      (C.r3Matrix sigma tau psi phi)
      ((cmp116Eq223CoordinateProjection S).mulVec x)
  calc
    C.r3RealSource sigma tau psi phi
          ((cmp116Eq223CoordinateProjection S).mulVec x) ⬝ᵥ
        C.r3RealSource sigma tau psi phi
          ((cmp116Eq223CoordinateProjection S).mulVec x) =
      (cmp116Eq214RealPartMatrix (C.r3Matrix sigma tau psi phi)).mulVec
          ((cmp116Eq223CoordinateProjection S).mulVec x) ⬝ᵥ
        (cmp116Eq214RealPartMatrix (C.r3Matrix sigma tau psi phi)).mulVec
          ((cmp116Eq223CoordinateProjection S).mulVec x) := by
      simp [r3RealSource, dotProduct]
    _ ≤ ‖C.r3Matrix sigma tau psi phi‖ *
          ‖(C.r3Matrix sigma tau psi phi).transpose‖ *
        (((cmp116Eq223CoordinateProjection S).mulVec x) ⬝ᵥ
          ((cmp116Eq223CoordinateProjection S).mulVec x)) := h
    _ = ‖C.r3Matrix sigma tau psi phi‖ *
          ‖(C.r3Matrix sigma tau psi phi).transpose‖ *
        ∑ i ∈ S, x i ^ 2 := by
      rw [dotProduct_projection_mulVec_self]

end

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
