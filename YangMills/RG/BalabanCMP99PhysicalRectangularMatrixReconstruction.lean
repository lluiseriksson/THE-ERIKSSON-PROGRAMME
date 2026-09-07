/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import YangMills.RG.BalabanCMP99SourcePi4ComplexMinimizerResponse

/-!
# Reconstruction of rectangular physical maps from complex matrices

The contour expansion is differentiated entrywise, while CMP102 equation
(80) consumes a real rectangular continuous linear map `F → E`.  This file
provides the finite-coordinate bridge for genuinely rectangular matrices.
It is the two-lattice analogue of the existing square endomorphism
reconstruction.
-/

namespace YangMills.RG

noncomputable section

/-- Entrywise real part for a rectangular complex matrix. -/
noncomputable def cmp99ComplexRectangularMatrixRealPart
    {ι κ : Type*} [Fintype ι] [Fintype κ] :
    Matrix ι κ ℂ → Matrix ι κ ℝ :=
  fun A i j => (A i j).re

/-- Real-linear reconstruction of physical rectangular maps from real
coordinate matrices. -/
noncomputable def cmp99PhysicalRectangularOfRealMatrixLinearMap
    {d N₁ N₂ Nc : ℕ} [NeZero N₁] [NeZero N₂]
    : Matrix (CMP116PhysicalWalkCoordinate d N₂ Nc)
        (CMP116PhysicalWalkCoordinate d N₁ Nc) ℝ →ₗ[ℝ]
      (PhysicalGaugeOneCochain d N₁ Nc →L[ℝ]
        PhysicalGaugeOneCochain d N₂ Nc) where
  toFun A := by
    let L :
        PhysicalGaugeOneCochain d N₁ Nc →ₗ[ℝ]
          PhysicalGaugeOneCochain d N₂ Nc :=
      cmp116PhysicalCoordinateLinearEquiv.toLinearMap.comp
        ((Matrix.toLin' A).comp
          cmp116PhysicalCoordinateLinearEquiv.symm.toLinearMap)
    exact L.toContinuousLinearMap
  map_add' A B := by
    apply ContinuousLinearMap.ext
    intro x
    apply cmp116PhysicalCoordinateLinearEquiv.symm.injective
    simp [LinearMap.comp_apply]
  map_smul' r A := by
    apply ContinuousLinearMap.ext
    intro x
    apply cmp116PhysicalCoordinateLinearEquiv.symm.injective
    simp [LinearMap.comp_apply]

/-- Reconstruct a real physical rectangular map from its real coordinate
matrix. -/
noncomputable def cmp99PhysicalRectangularOfRealMatrix
    {d N₁ N₂ Nc : ℕ} [NeZero N₁] [NeZero N₂]
    (A : Matrix (CMP116PhysicalWalkCoordinate d N₂ Nc)
      (CMP116PhysicalWalkCoordinate d N₁ Nc) ℝ) :
    PhysicalGaugeOneCochain d N₁ Nc →L[ℝ]
      PhysicalGaugeOneCochain d N₂ Nc :=
  cmp99PhysicalRectangularOfRealMatrixLinearMap A

/-- Reconstruction from a rectangular complex coordinate matrix.  Only
entrywise real parts are retained. -/
noncomputable def cmp99PhysicalRectangularOfComplexMatrix
    {d N₁ N₂ Nc : ℕ}
    [NeZero d] [NeZero N₁] [NeZero N₂] [NeZero (Nc ^ 2 - 1)] :
    Matrix (CMP116PhysicalWalkCoordinate d N₂ Nc)
        (CMP116PhysicalWalkCoordinate d N₁ Nc) ℂ →
      (PhysicalGaugeOneCochain d N₁ Nc →L[ℝ]
        PhysicalGaugeOneCochain d N₂ Nc) :=
  fun A =>
    cmp99PhysicalRectangularOfRealMatrix
      (cmp99ComplexRectangularMatrixRealPart A)

/-- Rectangular reconstruction is a left inverse of the canonical matrix
on every physical rectangular map. -/
@[simp]
theorem cmp99PhysicalRectangularOfComplexMatrixCLM_canonical
    {N₁ N₂ Nc : ℕ}
    [NeZero N₁] [NeZero N₂] [NeZero (Nc ^ 2 - 1)]
    (T : PhysicalGaugeOneCochain 4 N₁ Nc →L[ℝ]
      PhysicalGaugeOneCochain 4 N₂ Nc) :
    cmp99PhysicalRectangularOfComplexMatrix
        (cmp99PhysicalRectangularComplexMatrix T) = T := by
  apply ContinuousLinearMap.ext
  intro x
  apply cmp116PhysicalCoordinateLinearEquiv.symm.injective
  simp only [cmp99PhysicalRectangularOfComplexMatrix]
  change
    Matrix.toLin'
        (cmp99ComplexRectangularMatrixRealPart
          (cmp99PhysicalRectangularComplexMatrix T))
        (cmp116PhysicalCoordinateLinearEquiv.symm x) =
      cmp116PhysicalCoordinateLinearEquiv.symm (T x)
  have hreal :
      cmp99ComplexRectangularMatrixRealPart
          (cmp99PhysicalRectangularComplexMatrix T) =
        cmp99PhysicalRectangularRealMatrix T := by
    ext i j
    simp [cmp99ComplexRectangularMatrixRealPart,
      cmp99PhysicalRectangularComplexMatrix]
  rw [hreal, cmp99PhysicalRectangularRealMatrix,
    Matrix.toLin'_toMatrix']
  rfl

/-- Rectangular complex matrix unit. -/
def cmp99ComplexRectangularMatrixUnit
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (i : ι) (j : κ) : Matrix ι κ ℂ :=
  Pi.single i (Pi.single j 1)

/-- Rectangular reconstruction is the finite matrix-unit sum of the real
parts of all entries. -/
theorem cmp99PhysicalRectangularOfComplexMatrix_eq_sum_units
    {d N₁ N₂ Nc : ℕ}
    [NeZero d] [NeZero N₁] [NeZero N₂] [NeZero (Nc ^ 2 - 1)]
    (A : Matrix (CMP116PhysicalWalkCoordinate d N₂ Nc)
      (CMP116PhysicalWalkCoordinate d N₁ Nc) ℂ) :
    cmp99PhysicalRectangularOfComplexMatrix A =
      ∑ i, ∑ j, (A i j).re •
        cmp99PhysicalRectangularOfComplexMatrix
          (cmp99ComplexRectangularMatrixUnit i j) := by
  classical
  simp only [cmp99PhysicalRectangularOfComplexMatrix,
    cmp99PhysicalRectangularOfRealMatrix]
  simp_rw [← map_smul
    (cmp99PhysicalRectangularOfRealMatrixLinearMap
      (d := d) (N₁ := N₁) (N₂ := N₂) (Nc := Nc))]
  simp_rw [← map_sum
    (cmp99PhysicalRectangularOfRealMatrixLinearMap
      (d := d) (N₁ := N₁) (N₂ := N₂) (Nc := Nc))]
  apply congrArg
    (cmp99PhysicalRectangularOfRealMatrixLinearMap
      (d := d) (N₁ := N₁) (N₂ := N₂) (Nc := Nc))
  ext p q
  simp only [cmp99ComplexRectangularMatrixRealPart,
    Matrix.sum_apply,
    Matrix.smul_apply]
  rw [Finset.sum_eq_single p]
  · rw [Finset.sum_eq_single q]
    · simp [cmp99ComplexRectangularMatrixUnit]
    · intro b _ hb
      simp [cmp99ComplexRectangularMatrixUnit, hb]
    · simp
  · intro b _ hb
    simp [cmp99ComplexRectangularMatrixUnit, hb]
  · simp

/-- Entrywise real derivatives reconstruct to the derivative of the
rectangular physical map. -/
theorem
    hasDerivAt_cmp99PhysicalRectangularOfComplexMatrix_of_entrywise
    {d N₁ N₂ Nc : ℕ}
    [NeZero d] [NeZero N₁] [NeZero N₂] [NeZero (Nc ^ 2 - 1)]
    (A : ℝ → Matrix (CMP116PhysicalWalkCoordinate d N₂ Nc)
      (CMP116PhysicalWalkCoordinate d N₁ Nc) ℂ)
    (A' : Matrix (CMP116PhysicalWalkCoordinate d N₂ Nc)
      (CMP116PhysicalWalkCoordinate d N₁ Nc) ℂ)
    (t : ℝ)
    (hentry : ∀ i j,
      HasDerivAt (fun u => (A u i j).re) (A' i j).re t) :
    HasDerivAt
      (fun u => cmp99PhysicalRectangularOfComplexMatrix (A u))
      (cmp99PhysicalRectangularOfComplexMatrix A') t := by
  classical
  rw [show
    (fun u => cmp99PhysicalRectangularOfComplexMatrix (A u)) =
      fun u => ∑ i, ∑ j, (A u i j).re •
        cmp99PhysicalRectangularOfComplexMatrix
          (cmp99ComplexRectangularMatrixUnit i j) by
    funext u
    exact
      cmp99PhysicalRectangularOfComplexMatrix_eq_sum_units (A u)]
  rw [cmp99PhysicalRectangularOfComplexMatrix_eq_sum_units A']
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.fun_sum
  intro j _
  exact (hentry i j).smul_const
    (cmp99PhysicalRectangularOfComplexMatrix
      (cmp99ComplexRectangularMatrixUnit i j))

end

end YangMills.RG
