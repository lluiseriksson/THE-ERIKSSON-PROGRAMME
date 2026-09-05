/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214LogDeterminantDensity
import YangMills.RG.BalabanCMP116Eq214ContourRelativeNorm
import YangMills.RG.BalabanCMP116Eq214PhysicalContourWalkCovariance

/-!
# Installing physical walk precision and its determinant density

Precision and Gaussian normalization must be replaced together.  This module
installs a literal complex physical walk matrix as the contour precision and
constructs its determinant density from the explicit logarithmic determinant
ratio.  The structure's normalization identity is then proved, not assumed.

The only new conditions are the genuine non-singularity statements for the
base and contour precision matrices.  These are the finite-dimensional
consequences to be discharged from the already developed physical coercivity
and small-complex-contour estimates; they are not aliases for `(2.26)` or
`hRpoly`.
-/

namespace YangMills.RG

noncomputable section

universe u v

set_option synthInstance.maxHeartbeats 800000

open scoped Matrix.Norms.Operator

namespace CMP116Eq214PhysicalContourDensity

/-- Replace precision and determinant density simultaneously by the literal
physical walk matrix and its logarithmic determinant branch. -/
def withComplexPhysicalWalkPrecision
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
    (hbase : ∀ psi phi,
      (cmp116ComplexPhysicalWalkContourBaseMatrix
        emb active (term psi phi)).det ≠ 0)
    (hcontour : ∀ sigma psi phi,
      CMP116Eq214ShiftedPolydisc nDelta C.deltaRadius sigma →
      (cmp116ComplexPhysicalWalkContourMatrix
        emb active (term psi phi) sigma).det ≠ 0) :
    CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d N) Site Psi Phi E (Nc ^ 2 - 1) where
  spectatorSupport := C.spectatorSupport
  fluctuationSupport := C.fluctuationSupport
  deltaRadius := C.deltaRadius
  yRadius := C.yRadius
  referenceRoot := C.referenceRoot
  baseGamma := C.baseGamma
  contourGamma := C.contourGamma
  baseCovariance := C.baseCovariance
  contourCovariance := C.contourCovariance
  basePrecision := fun psi phi =>
    cmp116ComplexPhysicalWalkContourBaseMatrix emb active (term psi phi)
  contourPrecision := fun sigma _ psi phi =>
    cmp116ComplexPhysicalWalkContourMatrix emb active (term psi phi) sigma
  determinantDensity := fun sigma _ psi phi =>
    cmp116Eq214LogDeterminantDensity
      (cmp116ComplexPhysicalWalkContourBaseMatrix
        emb active (term psi phi))
      (cmp116ComplexPhysicalWalkContourMatrix
        emb active (term psi phi) sigma)
  potential := C.potential
  bondField := C.bondField
  threshold := C.threshold
  contourGamma_zero := C.contourGamma_zero
  contourCovariance_zero := C.contourCovariance_zero
  contourPrecision_zero := by
    intro psi phi
    exact cmp116ComplexPhysicalWalkContourMatrix_zero
      emb active (term psi phi)
  determinantDensity_zero := by
    intro psi phi
    exact cmp116Eq214LogDeterminantDensity_self
      (cmp116ComplexPhysicalWalkContourBaseMatrix
        emb active (term psi phi))
  determinantDensity_sq_mul_basePrecision_det := by
    intro sigma tau psi phi hsigma htau
    exact cmp116Eq214LogDeterminantDensity_sq_mul_base_det
      (cmp116ComplexPhysicalWalkContourBaseMatrix
        emb active (term psi phi))
      (cmp116ComplexPhysicalWalkContourMatrix
        emb active (term psi phi) sigma)
      (hbase psi phi) (hcontour sigma psi phi hsigma)
  potential_zero := C.potential_zero

/-- Install the literal physical precision using the quantitative Neumann
criterion on every complex contour.  Unlike
`withComplexPhysicalWalkPrecision`, this constructor does not receive contour
determinant nonvanishing: it derives it from the relative `L∞` operator-norm
defect against the coercive base precision. -/
def withComplexPhysicalWalkPrecisionOfRelativeNormLtOne
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
    (hbase : ∀ psi phi,
      (cmp116ComplexPhysicalWalkContourBaseMatrix
        emb active (term psi phi)).det ≠ 0)
    (hsmall : ∀ sigma psi phi,
      CMP116Eq214ShiftedPolydisc nDelta C.deltaRadius sigma →
      ‖(cmp116ComplexPhysicalWalkContourBaseMatrix
            emb active (term psi phi))⁻¹ *
          (cmp116ComplexPhysicalWalkContourMatrix
              emb active (term psi phi) sigma -
            cmp116ComplexPhysicalWalkContourBaseMatrix
              emb active (term psi phi))‖ < 1) :
    CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d N) Site Psi Phi E (Nc ^ 2 - 1) :=
  C.withComplexPhysicalWalkPrecision emb active term hbase fun sigma psi phi hsigma =>
    det_ne_zero_of_nonsingInv_mul_sub_norm_lt_one
      (cmp116ComplexPhysicalWalkContourBaseMatrix
        emb active (term psi phi))
      (cmp116ComplexPhysicalWalkContourMatrix
        emb active (term psi phi) sigma)
      (hbase psi phi) (hsmall sigma psi phi hsigma)

/-- Install the physical contour precision from the exact base
precision--covariance inverse identity and volume-uniform row bounds.

This is the source-facing constructor: neither a contour determinant nor the
base determinant nor the norm of an algebraic matrix inverse occurs in its
interface.  Base nonsingularity follows from the supplied exact
precision--covariance right-inverse identity. -/
def withComplexPhysicalWalkPrecisionOfCovarianceAndDefectBounds
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
    (covarianceBound defectBound : ℝ)
    (hbaseCovariance : ∀ psi phi,
      cmp116ComplexPhysicalWalkContourBaseMatrix
          emb active (term psi phi) *
        C.baseCovariance psi phi = 1)
    (hcovarianceBound : ∀ psi phi,
      ‖C.baseCovariance psi phi‖ ≤ covarianceBound)
    (hdefectBound : ∀ sigma psi phi,
      CMP116Eq214ShiftedPolydisc nDelta C.deltaRadius sigma →
      ‖cmp116ComplexPhysicalWalkContourMatrix
            emb active (term psi phi) sigma -
          cmp116ComplexPhysicalWalkContourBaseMatrix
            emb active (term psi phi)‖ ≤ defectBound)
    (hsmall : covarianceBound * defectBound < 1) :
    CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d N) Site Psi Phi E (Nc ^ 2 - 1) := by
  let hbase : ∀ psi phi,
      (cmp116ComplexPhysicalWalkContourBaseMatrix
        emb active (term psi phi)).det ≠ 0 :=
    fun psi phi =>
      Matrix.det_ne_zero_of_mul_eq_one
        (cmp116ComplexPhysicalWalkContourBaseMatrix
          emb active (term psi phi))
        (C.baseCovariance psi phi)
        (hbaseCovariance psi phi)
  exact C.withComplexPhysicalWalkPrecisionOfRelativeNormLtOne
    emb active term hbase fun sigma psi phi hsigma =>
      nonsingInv_mul_sub_norm_lt_one_of_covariance_bounds
        (cmp116ComplexPhysicalWalkContourBaseMatrix
          emb active (term psi phi))
        (cmp116ComplexPhysicalWalkContourMatrix
          emb active (term psi phi) sigma)
        (C.baseCovariance psi phi)
        covarianceBound defectBound
        (hbase psi phi) (hbaseCovariance psi phi)
        (hcovarianceBound psi phi)
        (hdefectBound sigma psi phi hsigma) hsmall

@[simp]
theorem withComplexPhysicalWalkPrecisionOfCovarianceAndDefectBounds_r2Matrix
    {Δ : Type u} {ω : Type v}
    {nDelta nY d N Nc : ℕ}
    {Site E : Type*} {Psi Phi : Site → Type*}
    [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d N) Site Psi Phi E (Nc ^ 2 - 1))
    (emb : Fin nDelta ↪ Δ) (active : ω → Finset Δ)
    (term :
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      ω → CMP116PhysicalWalkEndomorphism d N Nc)
    (covarianceBound defectBound : ℝ)
    (hbaseCovariance) (hcovarianceBound) (hdefectBound) (hsmall)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    (C.withComplexPhysicalWalkPrecisionOfCovarianceAndDefectBounds
        emb active term covarianceBound defectBound
        hbaseCovariance hcovarianceBound hdefectBound hsmall).r2Matrix
      sigma tau psi phi =
      cmp116ComplexPhysicalWalkContourBaseMatrix
          emb active (term psi phi) -
        cmp116ComplexPhysicalWalkContourMatrix
          emb active (term psi phi) sigma :=
  rfl

@[simp]
theorem withComplexPhysicalWalkPrecisionOfRelativeNormLtOne_r2Matrix
    {Δ : Type u} {ω : Type v}
    {nDelta nY d N Nc : ℕ}
    {Site E : Type*} {Psi Phi : Site → Type*}
    [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d N) Site Psi Phi E (Nc ^ 2 - 1))
    (emb : Fin nDelta ↪ Δ) (active : ω → Finset Δ)
    (term :
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      ω → CMP116PhysicalWalkEndomorphism d N Nc)
    (hbase) (hsmall)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    (C.withComplexPhysicalWalkPrecisionOfRelativeNormLtOne
        emb active term hbase hsmall).r2Matrix sigma tau psi phi =
      cmp116ComplexPhysicalWalkContourBaseMatrix
          emb active (term psi phi) -
        cmp116ComplexPhysicalWalkContourMatrix
          emb active (term psi phi) sigma :=
  rfl

@[simp]
theorem withComplexPhysicalWalkPrecision_basePrecision
    {Δ : Type u} {ω : Type v}
    {nDelta nY d N Nc : ℕ}
    {Site E : Type*} {Psi Phi : Site → Type*}
    [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d N) Site Psi Phi E (Nc ^ 2 - 1))
    (emb : Fin nDelta ↪ Δ) (active : ω → Finset Δ)
    (term :
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      ω → CMP116PhysicalWalkEndomorphism d N Nc)
    (hbase) (hcontour)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    (C.withComplexPhysicalWalkPrecision emb active term hbase hcontour).basePrecision
      psi phi =
      cmp116ComplexPhysicalWalkContourBaseMatrix
        emb active (term psi phi) :=
  rfl

@[simp]
theorem withComplexPhysicalWalkPrecision_contourPrecision
    {Δ : Type u} {ω : Type v}
    {nDelta nY d N Nc : ℕ}
    {Site E : Type*} {Psi Phi : Site → Type*}
    [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d N) Site Psi Phi E (Nc ^ 2 - 1))
    (emb : Fin nDelta ↪ Δ) (active : ω → Finset Δ)
    (term :
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      ω → CMP116PhysicalWalkEndomorphism d N Nc)
    (hbase) (hcontour)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    (C.withComplexPhysicalWalkPrecision emb active term hbase hcontour).contourPrecision
      sigma tau psi phi =
      cmp116ComplexPhysicalWalkContourMatrix
        emb active (term psi phi) sigma :=
  rfl

@[simp]
theorem withComplexPhysicalWalkPrecision_determinantDensity
    {Δ : Type u} {ω : Type v}
    {nDelta nY d N Nc : ℕ}
    {Site E : Type*} {Psi Phi : Site → Type*}
    [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d N) Site Psi Phi E (Nc ^ 2 - 1))
    (emb : Fin nDelta ↪ Δ) (active : ω → Finset Δ)
    (term :
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      ω → CMP116PhysicalWalkEndomorphism d N Nc)
    (hbase) (hcontour)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    (C.withComplexPhysicalWalkPrecision emb active term hbase hcontour).determinantDensity
      sigma tau psi phi =
      cmp116Eq214LogDeterminantDensity
        (cmp116ComplexPhysicalWalkContourBaseMatrix
          emb active (term psi phi))
        (cmp116ComplexPhysicalWalkContourMatrix
          emb active (term psi phi) sigma) :=
  rfl

/-- After simultaneous installation, `R2 = K0 - K1` is the literal
difference of the zero-contour and weakened physical precision matrices. -/
theorem withComplexPhysicalWalkPrecision_r2Matrix
    {Δ : Type u} {ω : Type v}
    {nDelta nY d N Nc : ℕ}
    {Site E : Type*} {Psi Phi : Site → Type*}
    [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d N) Site Psi Phi E (Nc ^ 2 - 1))
    (emb : Fin nDelta ↪ Δ) (active : ω → Finset Δ)
    (term :
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      ω → CMP116PhysicalWalkEndomorphism d N Nc)
    (hbase) (hcontour)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    (C.withComplexPhysicalWalkPrecision emb active term hbase hcontour).r2Matrix
      sigma tau psi phi =
      cmp116ComplexPhysicalWalkContourBaseMatrix
          emb active (term psi phi) -
        cmp116ComplexPhysicalWalkContourMatrix
          emb active (term psi phi) sigma :=
  rfl

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
