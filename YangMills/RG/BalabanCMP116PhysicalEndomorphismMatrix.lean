/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116ComplexPhysicalWalkMatrix
import YangMills.RG.BalabanCMP116SourcePi4ExactPatchedCovariance

/-!
# Exact matrices of physical one-cochain endomorphisms

The CMP116 determinant layer uses finite complex matrices, while the source
patched-parametrix identity is an equality of real continuous endomorphisms.
This file constructs the canonical bond--Lie coordinate matrix and proves
that it preserves composition and the identity exactly.

The entry theorem identifies the construction with the kernel coefficient
already used by the complex weakening series.  Consequently the matrix
inverse obtained here is in the same row/column convention as the contour
matrices: rows are target/output coordinates and columns are source/input
coordinates.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- Canonical linear equivalence between flattened bond--Lie scalars and a
physical positive-bond one-cochain. -/
noncomputable def cmp116PhysicalCoordinateLinearEquiv
    {d N Nc : ℕ} [NeZero N] :
    (CMP116PhysicalWalkCoordinate d N Nc → ℝ) ≃ₗ[ℝ]
      PhysicalGaugeOneCochain d N Nc where
  toFun x :=
    WithLp.toLp 2 fun bond =>
      (EuclideanSpace.equiv (Fin (Nc ^ 2 - 1)) ℝ).symm
        (fun a => x (bond, a))
  invFun A qa :=
    (EuclideanSpace.equiv (Fin (Nc ^ 2 - 1)) ℝ) (A qa.1) qa.2
  left_inv x := by
    funext qa
    rcases qa with ⟨bond, a⟩
    simp
  right_inv A := by
    apply PiLp.ext
    intro bond
    apply (EuclideanSpace.equiv (Fin (Nc ^ 2 - 1)) ℝ).injective
    funext a
    simp
  map_add' x y := by
    apply PiLp.ext
    intro bond
    apply (EuclideanSpace.equiv (Fin (Nc ^ 2 - 1)) ℝ).injective
    funext a
    simp
  map_smul' r x := by
    apply PiLp.ext
    intro bond
    apply (EuclideanSpace.equiv (Fin (Nc ^ 2 - 1)) ℝ).injective
    funext a
    simp

/-- A physical endomorphism transported to the flattened scalar function
space. -/
noncomputable def cmp116PhysicalEndomorphismFlatLinearMap
    {d N Nc : ℕ} [NeZero N]
    (T : PhysicalEndomorphism d N Nc) :
    (CMP116PhysicalWalkCoordinate d N Nc → ℝ) →ₗ[ℝ]
      (CMP116PhysicalWalkCoordinate d N Nc → ℝ) :=
  cmp116PhysicalCoordinateLinearEquiv.symm.toLinearMap.comp
    (T.toLinearMap.comp
      cmp116PhysicalCoordinateLinearEquiv.toLinearMap)

/-- Canonical real coordinate matrix of a physical endomorphism. -/
noncomputable def cmp116PhysicalEndomorphismRealMatrix
    {d N Nc : ℕ} [NeZero N]
    (T : PhysicalEndomorphism d N Nc) :
    Matrix (CMP116PhysicalWalkCoordinate d N Nc)
      (CMP116PhysicalWalkCoordinate d N Nc) ℝ :=
  LinearMap.toMatrix' (cmp116PhysicalEndomorphismFlatLinearMap T)

/-- Canonical complex coordinate matrix, obtained without changing any
physical coefficient. -/
noncomputable def cmp116PhysicalEndomorphismComplexMatrix
    {d N Nc : ℕ} [NeZero N]
    (T : PhysicalEndomorphism d N Nc) :
    Matrix (CMP116PhysicalWalkCoordinate d N Nc)
      (CMP116PhysicalWalkCoordinate d N Nc) ℂ :=
  (cmp116PhysicalEndomorphismRealMatrix T).map Complex.ofRealHom

@[simp]
theorem cmp116PhysicalCoordinateLinearEquiv_pi_single
    {d N Nc : ℕ} [NeZero N]
    (source : PhysicalBond d N) (input : Fin (Nc ^ 2 - 1)) :
    cmp116PhysicalCoordinateLinearEquiv
        (Pi.single (source, input) (1 : ℝ)) =
      singlePhysicalBondCochain source
        (EuclideanSpace.single input (1 : ℝ)) := by
  apply PiLp.ext
  intro bond
  apply (EuclideanSpace.equiv (Fin (Nc ^ 2 - 1)) ℝ).injective
  funext a
  by_cases hb : bond = source
  · subst bond
    by_cases ha : a = input
    · subst a
      simp [cmp116PhysicalCoordinateLinearEquiv,
        singlePhysicalBondCochain, Pi.single_apply]
    · simp [cmp116PhysicalCoordinateLinearEquiv,
        singlePhysicalBondCochain, Pi.single_apply, ha]
  · simp [cmp116PhysicalCoordinateLinearEquiv,
      singlePhysicalBondCochain, Pi.single_apply, hb]

theorem cmp116PhysicalEndomorphismFlatLinearMap_comp
    {d N Nc : ℕ} [NeZero N]
    (T S : PhysicalEndomorphism d N Nc) :
    cmp116PhysicalEndomorphismFlatLinearMap (T.comp S) =
      (cmp116PhysicalEndomorphismFlatLinearMap T).comp
        (cmp116PhysicalEndomorphismFlatLinearMap S) := by
  apply LinearMap.ext
  intro x
  apply cmp116PhysicalCoordinateLinearEquiv.injective
  simp [cmp116PhysicalEndomorphismFlatLinearMap,
    LinearMap.comp_apply, ContinuousLinearMap.comp_apply]

@[simp]
theorem cmp116PhysicalEndomorphismFlatLinearMap_id
    {d N Nc : ℕ} [NeZero N] :
    cmp116PhysicalEndomorphismFlatLinearMap
        (ContinuousLinearMap.id ℝ
          (PhysicalGaugeOneCochain d N Nc)) =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply cmp116PhysicalCoordinateLinearEquiv.injective
  simp [cmp116PhysicalEndomorphismFlatLinearMap,
    LinearMap.comp_apply]

theorem cmp116PhysicalEndomorphismRealMatrix_comp
    {d N Nc : ℕ} [NeZero N]
    (T S : PhysicalEndomorphism d N Nc) :
    cmp116PhysicalEndomorphismRealMatrix (T.comp S) =
      cmp116PhysicalEndomorphismRealMatrix T *
        cmp116PhysicalEndomorphismRealMatrix S := by
  rw [cmp116PhysicalEndomorphismRealMatrix,
    cmp116PhysicalEndomorphismFlatLinearMap_comp,
    LinearMap.toMatrix'_comp]
  rfl

@[simp]
theorem cmp116PhysicalEndomorphismRealMatrix_id
    {d N Nc : ℕ} [NeZero N] :
    cmp116PhysicalEndomorphismRealMatrix
        (ContinuousLinearMap.id ℝ
          (PhysicalGaugeOneCochain d N Nc)) = 1 := by
  rw [cmp116PhysicalEndomorphismRealMatrix,
    cmp116PhysicalEndomorphismFlatLinearMap_id,
    LinearMap.toMatrix'_id]

theorem cmp116PhysicalEndomorphismComplexMatrix_comp
    {d N Nc : ℕ} [NeZero N]
    (T S : PhysicalEndomorphism d N Nc) :
    cmp116PhysicalEndomorphismComplexMatrix (T.comp S) =
      cmp116PhysicalEndomorphismComplexMatrix T *
        cmp116PhysicalEndomorphismComplexMatrix S := by
  rw [cmp116PhysicalEndomorphismComplexMatrix,
    cmp116PhysicalEndomorphismRealMatrix_comp,
    Matrix.map_mul]
  rfl

@[simp]
theorem cmp116PhysicalEndomorphismComplexMatrix_id
    {d N Nc : ℕ} [NeZero N] :
    cmp116PhysicalEndomorphismComplexMatrix
        (ContinuousLinearMap.id ℝ
          (PhysicalGaugeOneCochain d N Nc)) = 1 := by
  simp [cmp116PhysicalEndomorphismComplexMatrix]

/-- The canonical matrix entry is literally the physical kernel coefficient
used throughout the complex source walk. -/
theorem cmp116PhysicalEndomorphismComplexMatrix_apply
    {d N Nc : ℕ}
    [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)]
    (T : PhysicalEndomorphism d N Nc)
    (row col : CMP116PhysicalWalkCoordinate d N Nc) :
    cmp116PhysicalEndomorphismComplexMatrix T row col =
      cmp116ComplexPhysicalOperatorCoefficient
        T col.1 row.1 col.2 row.2 := by
  rcases row with ⟨target, output⟩
  rcases col with ⟨source, input⟩
  rw [cmp116PhysicalEndomorphismComplexMatrix,
    Matrix.map_apply,
    cmp116PhysicalEndomorphismRealMatrix,
    LinearMap.toMatrix'_apply]
  change
    ((T (cmp116PhysicalCoordinateLinearEquiv
      (Pi.single (source, input) (1 : ℝ)))) target output : ℂ) =
      _
  rw [cmp116PhysicalCoordinateLinearEquiv_pi_single]
  rfl

/-- Matrix form of the exact source `Pi^4` inverse identity.  This closes the
operator-to-determinant coordinate bridge without assuming matrix
nonsingularity. -/
theorem cmp116SourcePi4_precision_mul_exactCovarianceMatrix_eq_one
    {M Q Nc : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism 4 (M * (2 * Q)) Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (Finset.univ : Finset (FinBox 4 Q))
          K
          (cmp99SourcePi4PhysicalBondSupport (M := M))
          (cmp99SourceBaseCellBondCore (M := M))
          hc hmass hK‖ < 1) :
    cmp116PhysicalEndomorphismComplexMatrix K *
        cmp116PhysicalEndomorphismComplexMatrix
          (cmp116SourcePi4ExactPatchedCovariance K hc hmass hK) =
      1 := by
  rw [← cmp116PhysicalEndomorphismComplexMatrix_comp,
    comp_cmp116SourcePi4ExactPatchedCovariance_eq_id_of_contraction
      K hc hmass hK hD]
  exact cmp116PhysicalEndomorphismComplexMatrix_id

end

end YangMills.RG
