/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import YangMills.RG.BalabanCMP116PhysicalEndomorphismMatrix

/-!
# Reconstruction of physical endomorphisms from complex coordinate matrices

The complex weakening expansion is differentiated entrywise, whereas the
CMP102 potential consumes real continuous endomorphisms.  This file provides
the missing honest bridge: take real parts, reconstruct the flattened real
linear map, and conjugate by the physical coordinate equivalence.

The terminal theorem proves that this continuous real-linear reconstruction
is a left inverse of the canonical complex matrix on every physical
endomorphism.  No equality between an arbitrary complex matrix and a physical
operator is asserted.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

local instance : ContinuousSMul ℝ ℂ := {
  continuous_smul := by
    simpa [Complex.real_smul] using
      (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd
}

/-- Entrywise real part, regarded as a real-linear map on complex matrices. -/
noncomputable def cmp116ComplexMatrixRealPartLinearMap
    {ι : Type*} [Fintype ι] :
    Matrix ι ι ℂ →ₗ[ℝ] Matrix ι ι ℝ where
  toFun A i j := (A i j).re
  map_add' A B := by
    ext i j
    simp
  map_smul' r A := by
    ext i j
    simp

/-- Reconstruct a real physical endomorphism from a real coordinate matrix. -/
noncomputable def cmp116PhysicalEndomorphismOfRealMatrix
    {d N Nc : ℕ} [NeZero N]
    (A : Matrix (CMP116PhysicalWalkCoordinate d N Nc)
      (CMP116PhysicalWalkCoordinate d N Nc) ℝ) :
    PhysicalEndomorphism d N Nc := by
  let L :
      PhysicalGaugeOneCochain d N Nc →ₗ[ℝ]
        PhysicalGaugeOneCochain d N Nc :=
    cmp116PhysicalCoordinateLinearEquiv.toLinearMap.comp
      ((Matrix.toLin' A).comp
        cmp116PhysicalCoordinateLinearEquiv.symm.toLinearMap)
  exact L.toContinuousLinearMap

/-- Continuous real-linear reconstruction from complex coordinate matrices.
Only the real part is retained. -/
noncomputable def cmp116PhysicalEndomorphismOfComplexMatrixCLM
    {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)] :
    Matrix (CMP116PhysicalWalkCoordinate d N Nc)
        (CMP116PhysicalWalkCoordinate d N Nc) ℂ →L[ℝ]
      PhysicalEndomorphism d N Nc := by
  let L :
      Matrix (CMP116PhysicalWalkCoordinate d N Nc)
          (CMP116PhysicalWalkCoordinate d N Nc) ℂ →ₗ[ℝ]
        PhysicalEndomorphism d N Nc := {
    toFun := fun A =>
      cmp116PhysicalEndomorphismOfRealMatrix
        (cmp116ComplexMatrixRealPartLinearMap A)
    map_add' := fun A B => by
      apply ContinuousLinearMap.ext
      intro x
      apply cmp116PhysicalCoordinateLinearEquiv.symm.injective
      simp [cmp116PhysicalEndomorphismOfRealMatrix,
        cmp116ComplexMatrixRealPartLinearMap, LinearMap.comp_apply]
      exact Matrix.add_mulVec _ _ _
    map_smul' := fun r A => by
      apply ContinuousLinearMap.ext
      intro x
      apply cmp116PhysicalCoordinateLinearEquiv.symm.injective
      simp [cmp116PhysicalEndomorphismOfRealMatrix,
        cmp116ComplexMatrixRealPartLinearMap, LinearMap.comp_apply]
  }
  have hL :
      Continuous
        (L :
          Matrix (CMP116PhysicalWalkCoordinate d N Nc)
              (CMP116PhysicalWalkCoordinate d N Nc) ℂ →
            PhysicalEndomorphism d N Nc) :=
    @LinearMap.continuous_of_finiteDimensional
      ℝ inferInstance
      (Matrix (CMP116PhysicalWalkCoordinate d N Nc)
        (CMP116PhysicalWalkCoordinate d N Nc) ℂ)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      (PhysicalEndomorphism d N Nc)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance (Module.Finite.matrix) L
  exact ⟨L, hL⟩

/-- Reconstruction is a left inverse of the canonical complex matrix on
physical endomorphisms. -/
@[simp]
theorem cmp116PhysicalEndomorphismOfComplexMatrixCLM_canonical
    {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)]
    (T : PhysicalEndomorphism d N Nc) :
    cmp116PhysicalEndomorphismOfComplexMatrixCLM
        (cmp116PhysicalEndomorphismComplexMatrix T) = T := by
  apply ContinuousLinearMap.ext
  intro x
  apply cmp116PhysicalCoordinateLinearEquiv.symm.injective
  simp only [cmp116PhysicalEndomorphismOfComplexMatrixCLM]
  change
    Matrix.toLin'
        (cmp116ComplexMatrixRealPartLinearMap
          (cmp116PhysicalEndomorphismComplexMatrix T))
        (cmp116PhysicalCoordinateLinearEquiv.symm x) =
      cmp116PhysicalCoordinateLinearEquiv.symm (T x)
  have hreal :
      cmp116ComplexMatrixRealPartLinearMap
          (cmp116PhysicalEndomorphismComplexMatrix T) =
        cmp116PhysicalEndomorphismRealMatrix T := by
    ext i j
    simp [cmp116ComplexMatrixRealPartLinearMap,
      cmp116PhysicalEndomorphismComplexMatrix]
  rw [hreal, cmp116PhysicalEndomorphismRealMatrix,
    Matrix.toLin'_toMatrix']
  rfl

/-- Complex matrix unit used to expand reconstruction into finitely many
real scalar coefficients. -/
def cmp116ComplexMatrixUnit
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) : Matrix ι ι ℂ :=
  Pi.single i (Pi.single j 1)

/-- Reconstruction is the finite sum of the real parts of the entries times
the reconstructed matrix units. -/
theorem cmp116PhysicalEndomorphismOfComplexMatrixCLM_eq_sum_units
    {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)]
    (A : Matrix (CMP116PhysicalWalkCoordinate d N Nc)
      (CMP116PhysicalWalkCoordinate d N Nc) ℂ) :
    cmp116PhysicalEndomorphismOfComplexMatrixCLM A =
      ∑ i, ∑ j, (A i j).re •
        cmp116PhysicalEndomorphismOfComplexMatrixCLM
          (cmp116ComplexMatrixUnit i j) := by
  classical
  simp_rw [← map_smul
    (cmp116PhysicalEndomorphismOfComplexMatrixCLM
      (d := d) (N := N) (Nc := Nc))]
  simp_rw [← map_sum
    (cmp116PhysicalEndomorphismOfComplexMatrixCLM
      (d := d) (N := N) (Nc := Nc))]
  change
    cmp116PhysicalEndomorphismOfRealMatrix
        (cmp116ComplexMatrixRealPartLinearMap A) =
      cmp116PhysicalEndomorphismOfRealMatrix
        (cmp116ComplexMatrixRealPartLinearMap
          (∑ i, ∑ j, (A i j).re • cmp116ComplexMatrixUnit i j))
  congr 1
  ext p q
  simp only [cmp116ComplexMatrixRealPartLinearMap, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.sum_apply, Matrix.smul_apply]
  rw [Finset.sum_eq_single p]
  · rw [Finset.sum_eq_single q]
    · simp [cmp116ComplexMatrixUnit]
    · intro b _ hb
      simp [cmp116ComplexMatrixUnit, hb]
    · simp
  · intro b _ hb
    simp [cmp116ComplexMatrixUnit, hb]
  · simp

/-- Entrywise real derivatives transport to the reconstructed physical
endomorphism.  The proof uses the finite matrix-unit expansion and therefore
does not require a normed-space instance for complex matrices over `ℝ`. -/
theorem
    hasDerivAt_cmp116PhysicalEndomorphismOfComplexMatrixCLM_of_entrywise
    {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)]
    (A : ℝ → Matrix (CMP116PhysicalWalkCoordinate d N Nc)
      (CMP116PhysicalWalkCoordinate d N Nc) ℂ)
    (A' : Matrix (CMP116PhysicalWalkCoordinate d N Nc)
      (CMP116PhysicalWalkCoordinate d N Nc) ℂ)
    (t : ℝ)
    (hentry : ∀ i j,
      HasDerivAt (fun u => (A u i j).re) (A' i j).re t) :
    HasDerivAt
      (fun u => cmp116PhysicalEndomorphismOfComplexMatrixCLM (A u))
      (cmp116PhysicalEndomorphismOfComplexMatrixCLM A') t := by
  classical
  rw [show
    (fun u => cmp116PhysicalEndomorphismOfComplexMatrixCLM (A u)) =
      fun u => ∑ i, ∑ j, (A u i j).re •
        cmp116PhysicalEndomorphismOfComplexMatrixCLM
          (cmp116ComplexMatrixUnit i j) by
    funext u
    exact
      cmp116PhysicalEndomorphismOfComplexMatrixCLM_eq_sum_units (A u)]
  rw [cmp116PhysicalEndomorphismOfComplexMatrixCLM_eq_sum_units A']
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.fun_sum
  intro j _
  exact (hentry i j).smul_const
    (cmp116PhysicalEndomorphismOfComplexMatrixCLM
      (cmp116ComplexMatrixUnit i j))

end

end YangMills.RG
