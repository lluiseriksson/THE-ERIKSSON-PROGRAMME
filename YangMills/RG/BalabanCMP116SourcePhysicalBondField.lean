/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePhysicalContourPotential

/-!
# Literal physical bond field in the CMP116 contour density

The large-field factor in equation (2.22) reads the `su(Nc)` value of the
Gaussian coordinate on each physical bond.  This module installs that map
literally and compares its selected energy with the ambient scalar energy.
-/

namespace YangMills.RG

open Matrix
open scoped BigOperators

noncomputable section

/-- The energy on any selected set of physical bonds is bounded by the full
scalar-coordinate energy. -/
theorem sum_norm_sq_cmp116SourcePhysicalCoordinateCochain_le
    {d N Nc : ℕ} [NeZero N]
    (P : Finset (PhysicalBond d N))
    (b : CMP116Eq214GaussianCoordinate
      (PhysicalBond d N) (Nc ^ 2 - 1)) :
    (∑ bond ∈ P, ‖cmp116SourcePhysicalCoordinateCochain b bond‖ ^ 2) ≤
      ∑ ba, b ba ^ 2 := by
  classical
  have hbond :
      ∀ bond : PhysicalBond d N,
        ‖cmp116SourcePhysicalCoordinateCochain b bond‖ ^ 2 =
          ∑ a : Fin (Nc ^ 2 - 1), b (bond, a) ^ 2 := by
    intro bond
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [cmp116SourcePhysicalCoordinateCochain,
      PhysicalGaugeCMP116Dictionary.sunLieCoordOfScalars]
  rw [Finset.sum_congr rfl fun bond _ => hbond bond]
  rw [show (∑ ba, b ba ^ 2) =
      ∑ bond : PhysicalBond d N,
        ∑ a : Fin (Nc ^ 2 - 1), b (bond, a) ^ 2 by
          simp only [Fintype.sum_prod_type]]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ P)
    (fun bond hbondP hbondNotP => by
      exact Finset.sum_nonneg fun a ha => sq_nonneg _)

namespace CMP116Eq214PhysicalContourDensity

/-- Install the literal source bond field and its physical threshold without
altering the contour, Gaussian, or potential data. -/
def withSourcePhysicalBondField
    {nDelta nY d N Nc : ℕ}
    {Site : Type*} {Psi Phi : Site → Type*}
    [NeZero N]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d N) Site Psi Phi (SUNLieCoord Nc) (Nc ^ 2 - 1))
    (threshold : ℝ) :
    CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d N) Site Psi Phi (SUNLieCoord Nc) (Nc ^ 2 - 1) where
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
  potential := C.potential
  bondField := fun b bond =>
    cmp116SourcePhysicalCoordinateCochain b bond
  threshold := threshold
  contourGamma_zero := C.contourGamma_zero
  contourCovariance_zero := C.contourCovariance_zero
  contourPrecision_zero := C.contourPrecision_zero
  determinantDensity_zero := C.determinantDensity_zero
  determinantDensity_sq_mul_basePrecision_det :=
    C.determinantDensity_sq_mul_basePrecision_det
  potential_zero := C.potential_zero

@[simp] theorem withSourcePhysicalBondField_bondField
    {nDelta nY d N Nc : ℕ}
    {Site : Type*} {Psi Phi : Site → Type*}
    [NeZero N]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d N) Site Psi Phi (SUNLieCoord Nc) (Nc ^ 2 - 1))
    (threshold : ℝ)
    (b : CMP116Eq214GaussianCoordinate
      (PhysicalBond d N) (Nc ^ 2 - 1))
    (bond : PhysicalBond d N) :
    (C.withSourcePhysicalBondField threshold).bondField b bond =
      cmp116SourcePhysicalCoordinateCochain b bond := by
  rfl

@[simp] theorem withSourcePhysicalBondField_threshold
    {nDelta nY d N Nc : ℕ}
    {Site : Type*} {Psi Phi : Site → Type*}
    [NeZero N]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d N) Site Psi Phi (SUNLieCoord Nc) (Nc ^ 2 - 1))
    (threshold : ℝ) :
    (C.withSourcePhysicalBondField threshold).threshold = threshold := by
  rfl

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
