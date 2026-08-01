/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.CoerciveCovariance
import YangMills.RG.FiniteDimensionalRealPositiveSqrt

/-!
# Positive square root of a symmetric coercive covariance

A strictly coercive finite-dimensional precision operator has an exact inverse
without any symmetry hypothesis.  To identify that inverse as a positive
operator and construct its positive square root, symmetry of the precision is
also required.  This module makes that boundary explicit and proves the full
operator-theoretic root package.

This file does not prove spatial localization or a quantitative root norm
bound.  Those are separate analytic obligations.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

/-- The inverse of a symmetric coercive precision operator is symmetric. -/
theorem covarianceOfIsCoerciveCLM_isSymmetric
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) (hSymm : A.IsSymmetric) :
    (covarianceOfIsCoerciveCLM A hc hA).IsSymmetric := by
  intro x y
  calc
    inner ℝ (covarianceOfIsCoerciveCLM A hc hA x) y =
        inner ℝ (covarianceOfIsCoerciveCLM A hc hA x)
          (A (covarianceOfIsCoerciveCLM A hc hA y)) := by
            rw [precision_apply_covarianceOfIsCoerciveCLM]
    _ = inner ℝ (A (covarianceOfIsCoerciveCLM A hc hA x))
          (covarianceOfIsCoerciveCLM A hc hA y) := by
            exact (hSymm _ _).symm
    _ = inner ℝ x (covarianceOfIsCoerciveCLM A hc hA y) := by
          rw [precision_apply_covarianceOfIsCoerciveCLM]

/-- The inverse of a symmetric coercive precision operator is positive. -/
theorem covarianceOfIsCoerciveCLM_isPositive
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) (hSymm : A.IsSymmetric) :
    (covarianceOfIsCoerciveCLM A hc hA).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff]
  refine ⟨covarianceOfIsCoerciveCLM_isSymmetric A hc hA hSymm, ?_⟩
  intro x
  rw [real_inner_comm]
  exact covarianceOfIsCoerciveCLM_psd A hc hA x

/-- Positive square root of the covariance of a symmetric coercive precision
operator. -/
noncomputable def covarianceSqrtOfIsCoerciveCLM
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) (hSymm : A.IsSymmetric) : E →L[ℝ] E :=
  finiteDimensionalRealPositiveSqrt
    (covarianceOfIsCoerciveCLM A hc hA)
    (covarianceOfIsCoerciveCLM_isPositive A hc hA hSymm)

/-- The covariance root squares exactly to the covariance. -/
theorem covarianceSqrtOfIsCoerciveCLM_comp_self
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) (hSymm : A.IsSymmetric) :
    (covarianceSqrtOfIsCoerciveCLM A hc hA hSymm).comp
      (covarianceSqrtOfIsCoerciveCLM A hc hA hSymm) =
        covarianceOfIsCoerciveCLM A hc hA := by
  exact finiteDimensionalRealPositiveSqrt_comp_self _ _

/-- The covariance root is positive. -/
theorem covarianceSqrtOfIsCoerciveCLM_isPositive
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) (hSymm : A.IsSymmetric) :
    (covarianceSqrtOfIsCoerciveCLM A hc hA hSymm).IsPositive := by
  exact finiteDimensionalRealPositiveSqrt_isPositive _ _

/-- Symmetry of the covariance root's bilinear form. -/
theorem covarianceSqrtOfIsCoerciveCLM_inner_left_eq_inner_right
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) (hSymm : A.IsSymmetric) (x y : E) :
    inner ℝ (covarianceSqrtOfIsCoerciveCLM A hc hA hSymm x) y =
      inner ℝ x (covarianceSqrtOfIsCoerciveCLM A hc hA hSymm y) := by
  exact finiteDimensionalRealPositiveSqrt_inner_left_eq_inner_right _ _ x y

/-- Nonnegativity of the covariance root's quadratic form. -/
theorem covarianceSqrtOfIsCoerciveCLM_inner_nonneg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) (hSymm : A.IsSymmetric) (x : E) :
    0 ≤ inner ℝ x (covarianceSqrtOfIsCoerciveCLM A hc hA hSymm x) := by
  exact finiteDimensionalRealPositiveSqrt_inner_nonneg _ _ x

end


end YangMills.RG
