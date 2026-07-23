/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214PhysicalContourWalkGamma

/-!
# Installing the physical walk matrix as the CMP116 contour covariance

The covariance entering `R1` is another source weakening expansion.  This
module installs its literal physical walk matrix in the contour density while
leaving Gamma, precision, determinant density, and potential unchanged.

Unlike precision, covariance has no determinant-normalization field in the
density structure, so this replacement is exact without an additional
analytic premise.  Precision will be installed only together with its
determinant density.
-/

namespace YangMills.RG

noncomputable section

universe u v

set_option synthInstance.maxHeartbeats 800000

namespace CMP116Eq214PhysicalContourDensity

/-- Replace the abstract covariance fields by a literal complex physical
random-walk matrix and its zero-contour base. -/
def withComplexPhysicalWalkCovariance
    {Δ : Type u} {ω : Type v}
    {nDelta nY d N Nc : ℕ}
    {Site E : Type*} {Psi Phi : Site → Type*}
    [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d N) Site Psi Phi E (Nc ^ 2 - 1))
    (emb : Fin nDelta ↪ Δ)
    (active : ω → Finset Δ)
    (term :
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      ω → CMP116PhysicalWalkEndomorphism d N Nc) :
    CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d N) Site Psi Phi E (Nc ^ 2 - 1) where
  spectatorSupport := C.spectatorSupport
  fluctuationSupport := C.fluctuationSupport
  deltaRadius := C.deltaRadius
  yRadius := C.yRadius
  referenceRoot := C.referenceRoot
  baseGamma := C.baseGamma
  contourGamma := C.contourGamma
  baseCovariance := fun psi phi =>
    cmp116ComplexPhysicalWalkContourBaseMatrix emb active (term psi phi)
  contourCovariance := fun sigma _ psi phi =>
    cmp116ComplexPhysicalWalkContourMatrix emb active (term psi phi) sigma
  basePrecision := C.basePrecision
  contourPrecision := C.contourPrecision
  determinantDensity := C.determinantDensity
  potential := C.potential
  bondField := C.bondField
  threshold := C.threshold
  contourGamma_zero := C.contourGamma_zero
  contourCovariance_zero := by
    intro psi phi
    exact cmp116ComplexPhysicalWalkContourMatrix_zero
      emb active (term psi phi)
  contourPrecision_zero := C.contourPrecision_zero
  determinantDensity_zero := C.determinantDensity_zero
  determinantDensity_sq_mul_basePrecision_det :=
    C.determinantDensity_sq_mul_basePrecision_det
  potential_zero := C.potential_zero

@[simp]
theorem withComplexPhysicalWalkCovariance_baseCovariance
    {Δ : Type u} {ω : Type v}
    {nDelta nY d N Nc : ℕ}
    {Site E : Type*} {Psi Phi : Site → Type*}
    [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d N) Site Psi Phi E (Nc ^ 2 - 1))
    (emb : Fin nDelta ↪ Δ)
    (active : ω → Finset Δ)
    (term :
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      ω → CMP116PhysicalWalkEndomorphism d N Nc)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    (C.withComplexPhysicalWalkCovariance emb active term).baseCovariance
        psi phi =
      cmp116ComplexPhysicalWalkContourBaseMatrix
        emb active (term psi phi) :=
  rfl

@[simp]
theorem withComplexPhysicalWalkCovariance_contourCovariance
    {Δ : Type u} {ω : Type v}
    {nDelta nY d N Nc : ℕ}
    {Site E : Type*} {Psi Phi : Site → Type*}
    [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d N) Site Psi Phi E (Nc ^ 2 - 1))
    (emb : Fin nDelta ↪ Δ)
    (active : ω → Finset Δ)
    (term :
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      ω → CMP116PhysicalWalkEndomorphism d N Nc)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    (C.withComplexPhysicalWalkCovariance emb active term).contourCovariance
        sigma tau psi phi =
      cmp116ComplexPhysicalWalkContourMatrix
        emb active (term psi phi) sigma :=
  rfl

/-- A radial physical operator estimate supplies the exact Cauchy boundary
certificate for every entry of the installed contour covariance. -/
theorem withComplexPhysicalWalkCovariance_entry_cauchyBoundary
    {Δ : Type u} {ω : Type v}
    {nDelta nY d N Nc : ℕ}
    {Site E : Type*} {Psi Phi : Site → Type*}
    [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d N) Site Psi Phi E (Nc ^ 2 - 1))
    (emb : Fin nDelta ↪ Δ)
    (active : ω → Finset Δ)
    (term :
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      ω → CMP116PhysicalWalkEndomorphism d N Nc)
    (radius : Fin nDelta → ℝ)
    (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (row col : CMP116PhysicalWalkCoordinate d N Nc)
    (R : ℝ)
    (hR : 1 ≤ R) (hcap : ∀ i, 1 + radius i ≤ R)
    (hsum : Summable fun walk =>
      R ^ (active walk).card • term psi phi walk) :
    CMP116Eq214CauchyBoundaryBound nDelta radius
      (fun sigma =>
        (C.withComplexPhysicalWalkCovariance emb active term).contourCovariance
          sigma tau psi phi row col)
      (∑' walk, R ^ (active walk).card *
        ‖cmp116ComplexPhysicalOperatorCoefficient
          (term psi phi walk) col.1 row.1 col.2 row.2‖) := by
  simpa using
    (cmp116Eq214CauchyBoundaryBound_of_complexPhysicalWalkMatrix_entry
      emb radius active (term psi phi) row col R hR hcap hsum)

/-- Installing both source walk families makes `R1` a literal sandwich of
the physical Gamma and covariance matrices, with their zero-contour bases.
No matrix-valued function remains abstract in this correction operator. -/
theorem withComplexPhysicalWalkGammaCovariance_r1Matrix
    {Δ : Type u} {ω : Type v}
    {nDelta nY d N Nc : ℕ}
    {Site E : Type*} {Psi Phi : Site → Type*}
    [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d N) Site Psi Phi E (Nc ^ 2 - 1))
    (emb : Fin nDelta ↪ Δ)
    (active : ω → Finset Δ)
    (gammaTerm covarianceTerm :
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      ω → CMP116PhysicalWalkEndomorphism d N Nc)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    ((C.withComplexPhysicalWalkGamma emb active gammaTerm
      ).withComplexPhysicalWalkCovariance emb active covarianceTerm).r1Matrix
        sigma tau psi phi =
      Matrix.transpose
          (cmp116ComplexPhysicalWalkContourMatrix
            emb active (gammaTerm psi phi) sigma) *
          cmp116ComplexPhysicalWalkContourMatrix
            emb active (covarianceTerm psi phi) sigma *
          cmp116ComplexPhysicalWalkContourMatrix
            emb active (gammaTerm psi phi) sigma -
        Matrix.transpose
          (cmp116ComplexPhysicalWalkContourBaseMatrix
            emb active (gammaTerm psi phi)) *
          cmp116ComplexPhysicalWalkContourBaseMatrix
            emb active (covarianceTerm psi phi) *
          cmp116ComplexPhysicalWalkContourBaseMatrix
            emb active (gammaTerm psi phi) :=
  rfl

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
