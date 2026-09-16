/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214PhysicalContourInnerDensity
import YangMills.RG.BalabanCMP116Eq220ComplexPotential

/-!
# Installing the literal CMP116 potential in the contour density

The complex density object separates the real reference Gaussian from all
contour deformation.  Its `potential` slot must nevertheless be tied to the
source expression in equation (2.14), rather than supplied as an arbitrary
analytic function.

This module replaces that slot by the literal finite sum

`sum Y in D, tau(Y) * ((1/2) <B,Q(Y,B)B> + V''_k(Y,B))`

evaluated on the canonical physical localization of the Gaussian coordinate.
All precision, covariance, Gamma and determinant data are inherited unchanged.
-/

namespace YangMills.RG

open Matrix

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

namespace CMP116Eq214PhysicalContourDensity

/-- Replace the abstract contour potential by the literal source potential
from equations (1.42) and (2.14). -/
def withPhysicalComplexTauPotential
    {nDelta nY d M N' Nc L lieDim : ℕ}
    {Site E : Type*} {Psi Phi : Site → Type*}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (Cube d L) Site Psi Phi E lieDim)
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (D : Finset (Fin nY))
    (quadratic :
      (Fin nDelta → ℂ) →
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      Fin nY → PhysicalGaugeOneCochain d (M * N') Nc →
        PhysicalEndomorphism d (M * N') Nc)
    (remainder :
      (Fin nDelta → ℂ) →
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      Fin nY → PhysicalGaugeOneCochain d (M * N') Nc → ℝ)
    (Z0 : Finset (FinBox d N')) :
    CMP116Eq214PhysicalContourDensity nDelta nY
      (Cube d L) Site Psi Phi E lieDim where
  spectatorSupport := C.spectatorSupport
  fluctuationSupport := C.fluctuationSupport
  deltaRadius := C.deltaRadius
  yRadius := C.yRadius
  referenceRoot := C.referenceRoot
  baseGamma := C.baseGamma
  contourGamma := C.contourGamma
  baseCovariance := C.baseCovariance
  contourCovariance := C.contourCovariance
  basePrecision := C.basePrecision
  contourPrecision := C.contourPrecision
  determinantDensity := C.determinantDensity
  potential := fun sigma tau psi phi b =>
    Dict.cmp116Eq214ComplexTauPotentialCoordinate
      D tau (quadratic sigma psi phi) (remainder sigma psi phi) Z0 b
  bondField := C.bondField
  threshold := C.threshold
  contourGamma_zero := C.contourGamma_zero
  contourCovariance_zero := C.contourCovariance_zero
  contourPrecision_zero := C.contourPrecision_zero
  determinantDensity_zero := C.determinantDensity_zero
  determinantDensity_sq_mul_basePrecision_det :=
    C.determinantDensity_sq_mul_basePrecision_det
  potential_zero := by
    intro psi phi b
    exact Dict.cmp116Eq214ComplexTauPotentialCoordinate_zero
      D (quadratic 0 psi phi) (remainder 0 psi phi) Z0 b

@[simp] theorem withPhysicalComplexTauPotential_potential
    {nDelta nY d M N' Nc L lieDim : ℕ}
    {Site E : Type*} {Psi Phi : Site → Type*}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (Cube d L) Site Psi Phi E lieDim)
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (D : Finset (Fin nY))
    (quadratic :
      (Fin nDelta → ℂ) →
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      Fin nY → PhysicalGaugeOneCochain d (M * N') Nc →
        PhysicalEndomorphism d (M * N') Nc)
    (remainder :
      (Fin nDelta → ℂ) →
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      Fin nY → PhysicalGaugeOneCochain d (M * N') Nc → ℝ)
    (Z0 : Finset (FinBox d N'))
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (b : CMP116Eq214GaussianCoordinate (Cube d L) lieDim) :
    (C.withPhysicalComplexTauPotential Dict D quadratic remainder Z0).potential
        sigma tau psi phi b =
      Dict.cmp116Eq214ComplexTauPotentialCoordinate
        D tau (quadratic sigma psi phi) (remainder sigma psi phi) Z0 b := by
  rfl

/-- Equation (2.20) applied directly to the potential installed in the
complex contour density.  Thus the bound and the density refer to the same
literal field, rather than to extensionally unrelated functions. -/
theorem re_withPhysicalComplexTauPotential_potential_le_projection
    {nDelta nY d M N' Nc L lieDim : ℕ}
    {Site E : Type*} {Psi Phi : Site → Type*}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (Cube d L) Site Psi Phi E lieDim)
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (D : Finset (Fin nY))
    (quadratic :
      (Fin nDelta → ℂ) →
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      Fin nY → PhysicalGaugeOneCochain d (M * N') Nc →
        PhysicalEndomorphism d (M * N') Nc)
    (remainder :
      (Fin nDelta → ℂ) →
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      Fin nY → PhysicalGaugeOneCochain d (M * N') Nc → ℝ)
    (amplitude residualWeight : Fin nY → ℝ)
    {kappa rowSum : ℝ}
    (hrowSum : 0 ≤ rowSum)
    (hrow : ∀ target : PhysicalBond d (M * N'),
      ∑ source : PhysicalBond d (M * N'),
        Real.exp (-(kappa * (physicalBondDist target source : ℝ))) ≤ rowSum)
    (Z0 : Finset (FinBox d N'))
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (b : CMP116Eq214GaussianCoordinate (Cube d L) lieDim)
    (hquadratic : ∀ y ∈ D,
      PhysicalCovarianceExponentialKernelBound
        (quadratic sigma psi phi y
          (physicalBondProjection
            (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
            (Dict.flatPhysicalLinearIsometryEquiv (WithLp.toLp 2 b))))
        physicalBondDist (amplitude y) kappa)
    (hremainder : ∀ y ∈ D,
      ‖tau y‖ *
          |remainder sigma psi phi y
            (physicalBondProjection
              (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
              (Dict.flatPhysicalLinearIsometryEquiv (WithLp.toLp 2 b)))| ≤
        residualWeight y) :
    ((C.withPhysicalComplexTauPotential
        Dict D quadratic remainder Z0).potential sigma tau psi phi b).re ≤
      (∑ y ∈ D, ‖tau y‖ * amplitude y * rowSum) / 2 *
          ((WithLp.toLp 2 b) ⬝ᵥ
            (cmp116Eq223CoordinateProjection
              (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ
                (WithLp.toLp 2 b))) +
        ∑ y ∈ D, residualWeight y := by
  exact Dict.re_cmp116Eq214ComplexTauPotentialCoordinate_le_projection
    D tau (quadratic sigma psi phi) (remainder sigma psi phi)
    amplitude residualWeight hrowSum hrow Z0 b hquadratic hremainder

/-- Installing the literal potential does not alter the three operator
corrections. -/
@[simp] theorem withPhysicalComplexTauPotential_r1Matrix
    {nDelta nY d M N' Nc L lieDim : ℕ}
    {Site E : Type*} {Psi Phi : Site → Type*}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (Cube d L) Site Psi Phi E lieDim)
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (D : Finset (Fin nY))
    (quadratic :
      (Fin nDelta → ℂ) →
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      Fin nY → PhysicalGaugeOneCochain d (M * N') Nc →
        PhysicalEndomorphism d (M * N') Nc)
    (remainder :
      (Fin nDelta → ℂ) →
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      Fin nY → PhysicalGaugeOneCochain d (M * N') Nc → ℝ)
    (Z0 : Finset (FinBox d N'))
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    (C.withPhysicalComplexTauPotential Dict D quadratic remainder Z0).r1Matrix
        sigma tau psi phi =
      C.r1Matrix sigma tau psi phi := by
  rfl

@[simp] theorem withPhysicalComplexTauPotential_r2Matrix
    {nDelta nY d M N' Nc L lieDim : ℕ}
    {Site E : Type*} {Psi Phi : Site → Type*}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (Cube d L) Site Psi Phi E lieDim)
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (D : Finset (Fin nY))
    (quadratic :
      (Fin nDelta → ℂ) →
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      Fin nY → PhysicalGaugeOneCochain d (M * N') Nc →
        PhysicalEndomorphism d (M * N') Nc)
    (remainder :
      (Fin nDelta → ℂ) →
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      Fin nY → PhysicalGaugeOneCochain d (M * N') Nc → ℝ)
    (Z0 : Finset (FinBox d N'))
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    (C.withPhysicalComplexTauPotential Dict D quadratic remainder Z0).r2Matrix
        sigma tau psi phi =
      C.r2Matrix sigma tau psi phi := by
  rfl

@[simp] theorem withPhysicalComplexTauPotential_r3Matrix
    {nDelta nY d M N' Nc L lieDim : ℕ}
    {Site E : Type*} {Psi Phi : Site → Type*}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (Cube d L) Site Psi Phi E lieDim)
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (D : Finset (Fin nY))
    (quadratic :
      (Fin nDelta → ℂ) →
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      Fin nY → PhysicalGaugeOneCochain d (M * N') Nc →
        PhysicalEndomorphism d (M * N') Nc)
    (remainder :
      (Fin nDelta → ℂ) →
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      Fin nY → PhysicalGaugeOneCochain d (M * N') Nc → ℝ)
    (Z0 : Finset (FinBox d N'))
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    (C.withPhysicalComplexTauPotential Dict D quadratic remainder Z0).r3Matrix
        sigma tau psi phi =
      C.r3Matrix sigma tau psi phi := by
  rfl

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
