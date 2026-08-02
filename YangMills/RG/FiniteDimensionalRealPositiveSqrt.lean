/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Order

/-!
# Positive square roots of finite-dimensional real continuous endomorphisms

This module constructs the positive square root of a positive continuous linear
endomorphism on a finite-dimensional real inner-product space.  The construction
is genuinely real: choose an orthonormal basis, diagonalize the resulting real
positive-semidefinite matrix, replace every eigenvalue `λ` by `Real.sqrt λ`, and
transport the matrix back to a continuous linear map.

The public API proves:

* positivity of the constructed root;
* the exact identity `root.comp root = T`;
* symmetry of the root's bilinear form;
* nonnegativity of its quadratic form;
* uniqueness among positive square roots.

No quantitative norm estimate is claimed here.  The finite-dimensional
hypothesis is essential to this implementation.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

open Matrix Unitary
open scoped ComplexOrder RealInnerProductSpace

noncomputable section

/-- Spectral positive square root of a real positive-semidefinite matrix. -/
private noncomputable def realPosSemidefMatrixRoot
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (hM : M.PosSemidef) : Matrix n n ℝ :=
  conjStarAlgAut ℝ _ hM.1.eigenvectorUnitary
    (Matrix.diagonal (RCLike.ofReal ∘ Real.sqrt ∘ hM.1.eigenvalues))

private theorem realPosSemidefMatrixRoot_posSemidef
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (hM : M.PosSemidef) :
    (realPosSemidefMatrixRoot M hM).PosSemidef := by
  let D : Matrix n n ℝ :=
    Matrix.diagonal (RCLike.ofReal ∘ Real.sqrt ∘ hM.1.eigenvalues)
  have hD : D.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    exact Real.sqrt_nonneg _
  change (hM.1.eigenvectorUnitary : Matrix n n ℝ) * D *
    star (hM.1.eigenvectorUnitary : Matrix n n ℝ) |>.PosSemidef
  exact hD.mul_mul_conjTranspose_same
    (hM.1.eigenvectorUnitary : Matrix n n ℝ)

private theorem realPosSemidefMatrixRoot_mul_self
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (hM : M.PosSemidef) :
    realPosSemidefMatrixRoot M hM * realPosSemidefMatrixRoot M hM = M := by
  let U := hM.1.eigenvectorUnitary
  let D : Matrix n n ℝ :=
    Matrix.diagonal (RCLike.ofReal ∘ Real.sqrt ∘ hM.1.eigenvalues)
  change conjStarAlgAut ℝ _ U D * conjStarAlgAut ℝ _ U D = M
  rw [← map_mul]
  have hDD : D * D =
      Matrix.diagonal (RCLike.ofReal ∘ hM.1.eigenvalues) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq]
    exact Real.mul_self_sqrt (hM.eigenvalues_nonneg i)
  rw [hDD]
  exact hM.1.spectral_theorem.symm

/-- Positive square root of a positive continuous linear endomorphism on a
finite-dimensional real inner-product space. -/
noncomputable def finiteDimensionalRealPositiveSqrt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (T : E →L[ℝ] E) (hT : T.IsPositive) : E →L[ℝ] E := by
  classical
  let b := stdOrthonormalBasis ℝ E
  let M := LinearMap.toMatrixAlgEquiv b.toBasis T.toLinearMap
  have hM : M.PosSemidef := by
    apply (LinearMap.posSemidef_toMatrix_iff b).2
    exact (ContinuousLinearMap.isPositive_toLinearMap_iff T).2 hT
  exact (Matrix.toLinAlgEquiv b.toBasis
    (realPosSemidefMatrixRoot M hM)).toContinuousLinearMap

/-- The spectral square root is positive. -/
theorem finiteDimensionalRealPositiveSqrt_isPositive
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (T : E →L[ℝ] E) (hT : T.IsPositive) :
    (finiteDimensionalRealPositiveSqrt T hT).IsPositive := by
  classical
  let b := stdOrthonormalBasis ℝ E
  let M := LinearMap.toMatrixAlgEquiv b.toBasis T.toLinearMap
  have hM : M.PosSemidef := by
    apply (LinearMap.posSemidef_toMatrix_iff b).2
    exact (ContinuousLinearMap.isPositive_toLinearMap_iff T).2 hT
  change (Matrix.toLinAlgEquiv b.toBasis
    (realPosSemidefMatrixRoot M hM)).toContinuousLinearMap.IsPositive
  rw [LinearMap.isPositive_toContinuousLinearMap_iff]
  apply (LinearMap.posSemidef_toMatrix_iff b).mp
  change (LinearMap.toMatrix b.toBasis b.toBasis
    (Matrix.toLin b.toBasis b.toBasis
      (realPosSemidefMatrixRoot M hM))).PosSemidef
  rw [LinearMap.toMatrix_toLin]
  exact realPosSemidefMatrixRoot_posSemidef M hM

/-- The spectral square root squares exactly to the original endomorphism. -/
theorem finiteDimensionalRealPositiveSqrt_comp_self
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (T : E →L[ℝ] E) (hT : T.IsPositive) :
    (finiteDimensionalRealPositiveSqrt T hT).comp
      (finiteDimensionalRealPositiveSqrt T hT) = T := by
  classical
  let b := stdOrthonormalBasis ℝ E
  let M := LinearMap.toMatrixAlgEquiv b.toBasis T.toLinearMap
  have hM : M.PosSemidef := by
    apply (LinearMap.posSemidef_toMatrix_iff b).2
    exact (ContinuousLinearMap.isPositive_toLinearMap_iff T).2 hT
  let S := realPosSemidefMatrixRoot M hM
  let rootLin := Matrix.toLinAlgEquiv b.toBasis S
  have hsqM : S * S = M :=
    realPosSemidefMatrixRoot_mul_self M hM
  have hlin : rootLin.comp rootLin = T.toLinearMap := by
    calc
      rootLin.comp rootLin = Matrix.toLinAlgEquiv b.toBasis (S * S) := by
        exact (Matrix.toLinAlgEquiv_mul b.toBasis S S).symm
      _ = Matrix.toLinAlgEquiv b.toBasis M := congrArg _ hsqM
      _ = T.toLinearMap := by
        exact Matrix.toLinAlgEquiv_toMatrixAlgEquiv b.toBasis T.toLinearMap
  apply ContinuousLinearMap.ext
  intro x
  change (rootLin.comp rootLin) x = T.toLinearMap x
  rw [hlin]

/-- Symmetry of the bilinear form of the spectral square root. -/
theorem finiteDimensionalRealPositiveSqrt_inner_left_eq_inner_right
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (T : E →L[ℝ] E) (hT : T.IsPositive) (x y : E) :
    inner ℝ (finiteDimensionalRealPositiveSqrt T hT x) y =
      inner ℝ x (finiteDimensionalRealPositiveSqrt T hT y) :=
  (finiteDimensionalRealPositiveSqrt_isPositive T hT).isSymmetric x y

/-- Nonnegativity of the quadratic form of the spectral square root. -/
theorem finiteDimensionalRealPositiveSqrt_inner_nonneg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (T : E →L[ℝ] E) (hT : T.IsPositive) (x : E) :
    0 ≤ inner ℝ x (finiteDimensionalRealPositiveSqrt T hT x) :=
  (finiteDimensionalRealPositiveSqrt_isPositive T hT).inner_nonneg_right x

/-- Positive square roots of a continuous endomorphism are unique in finite
real dimension.  This formulation avoids exposing the coordinate-level
spectral construction and is the bridge used by integral representations. -/
theorem eq_of_isPositive_of_comp_self_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {S R T : E →L[ℝ] E}
    (hS : S.IsPositive) (hR : R.IsPositive)
    (hST : S.comp S = T) (hRT : R.comp R = T) : S = R := by
  classical
  let b := stdOrthonormalBasis ℝ E
  let MS := LinearMap.toMatrixAlgEquiv b.toBasis S.toLinearMap
  let MR := LinearMap.toMatrixAlgEquiv b.toBasis R.toLinearMap
  have hMS : MS.PosSemidef := by
    apply (LinearMap.posSemidef_toMatrix_iff b).2
    exact (ContinuousLinearMap.isPositive_toLinearMap_iff S).2 hS
  have hMR : MR.PosSemidef := by
    apply (LinearMap.posSemidef_toMatrix_iff b).2
    exact (ContinuousLinearMap.isPositive_toLinearMap_iff R).2 hR
  have hcomp : S.comp S = R.comp R := hST.trans hRT.symm
  have hsq : MS * MS = MR * MR := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact congrArg (fun L : E →L[ℝ] E => L.toLinearMap) hcomp
  have hmat : MS = MR := by
    exact (hMS.sq_eq_sq_iff hMR).mp (by simpa [pow_two] using hsq)
  have hlin : S.toLinearMap = R.toLinearMap :=
    (LinearMap.toMatrixAlgEquiv b.toBasis).injective hmat
  exact ContinuousLinearMap.ext fun x => LinearMap.congr_fun hlin x

end

end YangMills.RG
