/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99PhysicalRectangularMatrixReconstruction

/-!
# Continuous additive reconstruction of rectangular complex matrices

The literal CMP99 walk expansion is naturally a convergent series of
rectangular complex matrices. CMP102 equation (80), on the physical real
axis, consumes real continuous linear maps. This module packages the
existing entrywise-real reconstruction as a continuous additive map.

Additivity and continuity are exactly what is needed to transport finite
sums and genuinely summable series. No claim is made that matrices away
from the real contour have real entries.
-/

namespace YangMills.RG

noncomputable section

/-- Entrywise-real reconstruction is additive on rectangular complex
matrices. -/
noncomputable def cmp99PhysicalRectangularOfComplexMatrixAddHom
    {d N₁ N₂ Nc : ℕ}
    [NeZero d] [NeZero N₁] [NeZero N₂] [NeZero (Nc ^ 2 - 1)] :
    Matrix (CMP116PhysicalWalkCoordinate d N₂ Nc)
        (CMP116PhysicalWalkCoordinate d N₁ Nc) ℂ →+
      (PhysicalGaugeOneCochain d N₁ Nc →L[ℝ]
        PhysicalGaugeOneCochain d N₂ Nc) where
  toFun := cmp99PhysicalRectangularOfComplexMatrix
  map_zero' := by
    change
      cmp99PhysicalRectangularOfRealMatrixLinearMap
          (cmp99ComplexRectangularMatrixRealPart 0) = 0
    rw [show cmp99ComplexRectangularMatrixRealPart
        (0 : Matrix (CMP116PhysicalWalkCoordinate d N₂ Nc)
          (CMP116PhysicalWalkCoordinate d N₁ Nc) ℂ) = 0 by
      ext i j
      rfl]
    exact
      (cmp99PhysicalRectangularOfRealMatrixLinearMap
        (d := d) (N₁ := N₁) (N₂ := N₂) (Nc := Nc)).map_zero
  map_add' A B := by
    change
      cmp99PhysicalRectangularOfRealMatrixLinearMap
          (cmp99ComplexRectangularMatrixRealPart (A + B)) =
        cmp99PhysicalRectangularOfRealMatrixLinearMap
            (cmp99ComplexRectangularMatrixRealPart A) +
          cmp99PhysicalRectangularOfRealMatrixLinearMap
            (cmp99ComplexRectangularMatrixRealPart B)
    rw [show cmp99ComplexRectangularMatrixRealPart (A + B) =
        cmp99ComplexRectangularMatrixRealPart A +
          cmp99ComplexRectangularMatrixRealPart B by
      ext i j
      exact Complex.add_re _ _]
    exact
      (cmp99PhysicalRectangularOfRealMatrixLinearMap
        (d := d) (N₁ := N₁) (N₂ := N₂) (Nc := Nc)).map_add _ _

/-- Reconstruction is continuous: it is a finite sum of continuous real
entry evaluations multiplied by fixed physical matrix units. -/
theorem continuous_cmp99PhysicalRectangularOfComplexMatrix
    {d N₁ N₂ Nc : ℕ}
    [NeZero d] [NeZero N₁] [NeZero N₂] [NeZero (Nc ^ 2 - 1)] :
    Continuous
      (cmp99PhysicalRectangularOfComplexMatrix :
        Matrix (CMP116PhysicalWalkCoordinate d N₂ Nc)
            (CMP116PhysicalWalkCoordinate d N₁ Nc) ℂ →
          (PhysicalGaugeOneCochain d N₁ Nc →L[ℝ]
            PhysicalGaugeOneCochain d N₂ Nc)) := by
  classical
  rw [show
    (cmp99PhysicalRectangularOfComplexMatrix :
      Matrix (CMP116PhysicalWalkCoordinate d N₂ Nc)
          (CMP116PhysicalWalkCoordinate d N₁ Nc) ℂ →
        (PhysicalGaugeOneCochain d N₁ Nc →L[ℝ]
          PhysicalGaugeOneCochain d N₂ Nc)) =
      fun A => ∑ i, ∑ j, (A i j).re •
        cmp99PhysicalRectangularOfComplexMatrix
          (cmp99ComplexRectangularMatrixUnit i j) by
    funext A
    exact cmp99PhysicalRectangularOfComplexMatrix_eq_sum_units A]
  fun_prop

/-- Continuous additive reconstruction of rectangular complex matrices. -/
noncomputable def cmp99PhysicalRectangularOfComplexMatrixContinuousAddHom
    {d N₁ N₂ Nc : ℕ}
    [NeZero d] [NeZero N₁] [NeZero N₂] [NeZero (Nc ^ 2 - 1)] :
    Matrix (CMP116PhysicalWalkCoordinate d N₂ Nc)
        (CMP116PhysicalWalkCoordinate d N₁ Nc) ℂ →ₜ+
      (PhysicalGaugeOneCochain d N₁ Nc →L[ℝ]
        PhysicalGaugeOneCochain d N₂ Nc) :=
  ContinuousAddMonoidHom.mk
    cmp99PhysicalRectangularOfComplexMatrixAddHom
    continuous_cmp99PhysicalRectangularOfComplexMatrix

@[simp]
theorem cmp99PhysicalRectangularOfComplexMatrixContinuousAddHom_apply
    {d N₁ N₂ Nc : ℕ}
    [NeZero d] [NeZero N₁] [NeZero N₂] [NeZero (Nc ^ 2 - 1)]
    (A : Matrix (CMP116PhysicalWalkCoordinate d N₂ Nc)
      (CMP116PhysicalWalkCoordinate d N₁ Nc) ℂ) :
    cmp99PhysicalRectangularOfComplexMatrixContinuousAddHom A =
      cmp99PhysicalRectangularOfComplexMatrix A :=
  rfl

/-- Reconstruction commutes with finite matrix sums. -/
theorem cmp99PhysicalRectangularOfComplexMatrix_sum
    {d N₁ N₂ Nc : ℕ} {ι : Type*} [Fintype ι]
    [NeZero d] [NeZero N₁] [NeZero N₂] [NeZero (Nc ^ 2 - 1)]
    (A : ι → Matrix (CMP116PhysicalWalkCoordinate d N₂ Nc)
      (CMP116PhysicalWalkCoordinate d N₁ Nc) ℂ) :
    cmp99PhysicalRectangularOfComplexMatrix (∑ i, A i) =
      ∑ i, cmp99PhysicalRectangularOfComplexMatrix (A i) := by
  simpa only [
    cmp99PhysicalRectangularOfComplexMatrixContinuousAddHom_apply] using
    (map_sum
      cmp99PhysicalRectangularOfComplexMatrixContinuousAddHom A Finset.univ)

/-- Reconstruction preserves summability. -/
theorem summable_cmp99PhysicalRectangularOfComplexMatrix
    {d N₁ N₂ Nc : ℕ}
    [NeZero d] [NeZero N₁] [NeZero N₂] [NeZero (Nc ^ 2 - 1)]
    {ι : Type*}
    (A : ι → Matrix (CMP116PhysicalWalkCoordinate d N₂ Nc)
      (CMP116PhysicalWalkCoordinate d N₁ Nc) ℂ)
    (hA : Summable A) :
    Summable fun i => cmp99PhysicalRectangularOfComplexMatrix (A i) := by
  simpa only [Function.comp_apply,
    cmp99PhysicalRectangularOfComplexMatrixContinuousAddHom_apply] using
    hA.map cmp99PhysicalRectangularOfComplexMatrixContinuousAddHom
      cmp99PhysicalRectangularOfComplexMatrixContinuousAddHom.continuous

/-- Reconstruction commutes with a genuinely summable rectangular matrix
series. -/
theorem cmp99PhysicalRectangularOfComplexMatrix_tsum
    {d N₁ N₂ Nc : ℕ}
    [NeZero d] [NeZero N₁] [NeZero N₂] [NeZero (Nc ^ 2 - 1)]
    {ι : Type*}
    (A : ι → Matrix (CMP116PhysicalWalkCoordinate d N₂ Nc)
      (CMP116PhysicalWalkCoordinate d N₁ Nc) ℂ)
    (hA : Summable A) :
    cmp99PhysicalRectangularOfComplexMatrix (∑' i, A i) =
      ∑' i, cmp99PhysicalRectangularOfComplexMatrix (A i) := by
  have hsum :=
    hA.hasSum.map
      cmp99PhysicalRectangularOfComplexMatrixContinuousAddHom
      cmp99PhysicalRectangularOfComplexMatrixContinuousAddHom.continuous
  simpa only [Function.comp_apply,
    cmp99PhysicalRectangularOfComplexMatrixContinuousAddHom_apply] using
    hsum.tsum_eq.symm

end

end YangMills.RG
