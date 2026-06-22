/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.CoercivePerturbation

/-!
# Exact finite-dimensional covariance from coercivity

This module closes the deterministic bridge between the gauge-precision layer
and the future physical Gaussian fluctuation measure.  A strictly coercive
continuous linear endomorphism on a finite-dimensional real inner-product
space is injective, hence bijective, and therefore has an exact continuous
linear inverse.  We name that inverse `covarianceOfIsCoerciveCLM` and prove:

* both exact inverse identities;
* the pointwise lower bound `c * ‖x‖ ≤ ‖A x‖`;
* the pointwise covariance estimate `‖C y‖ ≤ ‖y‖ / c`;
* the operator bound `‖C‖ ≤ c⁻¹`;
* positivity of the inverse quadratic form.

The intended downstream instantiation is the gauge-fixed precision operator
constructed from the Yang--Mills Hessian, gauge-fixing term, and block mass.
This file does not construct that physical operator, prove propagator decay,
construct a covariance square root, or produce CMP116 activities.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

/-- Coercivity controls the norm of the image from below:
`c * ‖x‖ ≤ ‖A x‖`.

No sign assumption on `c` is needed for this algebraic inequality. -/
theorem isCoerciveCLM_norm_lower_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E) {c : ℝ}
    (hA : IsCoerciveCLM A c) (x : E) :
    c * ‖x‖ ≤ ‖A x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  · have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hinner :
        inner ℝ x (A x) ≤ ‖x‖ * ‖A x‖ :=
      (le_abs_self _).trans (abs_real_inner_le_norm x (A x))
    have hquad :
        c * ‖x‖ ^ 2 ≤ ‖x‖ * ‖A x‖ :=
      (hA x).trans hinner
    have hmul :
        ‖x‖ * (c * ‖x‖) ≤ ‖x‖ * ‖A x‖ := by
      calc
        ‖x‖ * (c * ‖x‖) = c * ‖x‖ ^ 2 := by ring
        _ ≤ ‖x‖ * ‖A x‖ := hquad
    exact le_of_mul_le_mul_left hmul hxnorm

/-- Strict coercivity forces injectivity. -/
theorem isCoerciveCLM_injective
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) :
    Function.Injective A := by
  intro x y hxy
  have hzero : A (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hcoer : c * ‖x - y‖ ^ 2 ≤ 0 := by
    simpa [hzero] using hA (x - y)
  have hnonneg : 0 ≤ c * ‖x - y‖ ^ 2 :=
    mul_nonneg hc.le (sq_nonneg ‖x - y‖)
  have hprod : c * ‖x - y‖ ^ 2 = 0 :=
    le_antisymm hcoer hnonneg
  have hsquare : ‖x - y‖ ^ 2 = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hc)
  have hnorm : ‖x - y‖ = 0 :=
    sq_eq_zero_iff.mp hsquare
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- In finite dimension, strict coercivity also forces surjectivity. -/
theorem isCoerciveCLM_surjective
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) :
    Function.Surjective A := by
  have hinj : Function.Injective A.toLinearMap := by
    intro x y hxy
    exact isCoerciveCLM_injective A hc hA hxy
  simpa using
    ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := A.toLinearMap) rfl).mp hinj)

/-- A strictly coercive finite-dimensional precision operator, regarded as a
continuous linear equivalence. -/
noncomputable def continuousLinearEquivOfIsCoerciveCLM
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) :
    E ≃L[ℝ] E :=
  (A.toLinearMap.linearEquivOfInjective
    (by
      intro x y hxy
      exact isCoerciveCLM_injective A hc hA hxy)
    rfl).toContinuousLinearEquiv

@[simp]
theorem continuousLinearEquivOfIsCoerciveCLM_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) (x : E) :
    continuousLinearEquivOfIsCoerciveCLM A hc hA x = A x := by
  rfl

/-- The exact finite-dimensional covariance associated with a strictly
coercive precision operator. -/
noncomputable def covarianceOfIsCoerciveCLM
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) :
    E →L[ℝ] E :=
  (continuousLinearEquivOfIsCoerciveCLM A hc hA).symm.toContinuousLinearMap

/-- The covariance is a left inverse to the precision operator. -/
@[simp]
theorem covarianceOfIsCoerciveCLM_apply_precision
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) (x : E) :
    covarianceOfIsCoerciveCLM A hc hA (A x) = x := by
  change
    (continuousLinearEquivOfIsCoerciveCLM A hc hA).symm
      (continuousLinearEquivOfIsCoerciveCLM A hc hA x) = x
  exact (continuousLinearEquivOfIsCoerciveCLM A hc hA).symm_apply_apply x

/-- The covariance is a right inverse to the precision operator. -/
@[simp]
theorem precision_apply_covarianceOfIsCoerciveCLM
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) (y : E) :
    A (covarianceOfIsCoerciveCLM A hc hA y) = y := by
  change
    continuousLinearEquivOfIsCoerciveCLM A hc hA
      ((continuousLinearEquivOfIsCoerciveCLM A hc hA).symm y) = y
  exact (continuousLinearEquivOfIsCoerciveCLM A hc hA).apply_symm_apply y

/-- Exact left-inverse identity at the operator level. -/
theorem covarianceOfIsCoerciveCLM_comp_precision
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) :
    (covarianceOfIsCoerciveCLM A hc hA).comp A =
      ContinuousLinearMap.id ℝ E := by
  ext x
  exact covarianceOfIsCoerciveCLM_apply_precision A hc hA x

/-- Exact right-inverse identity at the operator level. -/
theorem precision_comp_covarianceOfIsCoerciveCLM
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) :
    A.comp (covarianceOfIsCoerciveCLM A hc hA) =
      ContinuousLinearMap.id ℝ E := by
  ext y
  exact precision_apply_covarianceOfIsCoerciveCLM A hc hA y

/-- Pointwise covariance bound obtained directly from the coercivity constant. -/
theorem norm_covarianceOfIsCoerciveCLM_apply_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) (y : E) :
    ‖covarianceOfIsCoerciveCLM A hc hA y‖ ≤ ‖y‖ / c := by
  apply (le_div_iff₀ hc).2
  have hbound :=
    isCoerciveCLM_norm_lower_bound A hA
      (covarianceOfIsCoerciveCLM A hc hA y)
  simpa [mul_comm] using hbound

/-- Operator-norm covariance bound `‖A⁻¹‖ ≤ c⁻¹`. -/
theorem norm_covarianceOfIsCoerciveCLM_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) :
    ‖covarianceOfIsCoerciveCLM A hc hA‖ ≤ c⁻¹ := by
  refine ContinuousLinearMap.opNorm_le_bound
    (covarianceOfIsCoerciveCLM A hc hA) (inv_nonneg.mpr hc.le) ?_
  intro y
  have hbound := norm_covarianceOfIsCoerciveCLM_apply_le A hc hA y
  simpa [div_eq_mul_inv, mul_comm] using hbound

/-- The inverse of a strictly coercive real precision operator has a
nonnegative quadratic form.  Self-adjointness is not needed for this statement:
write `y = A x` and use symmetry of the real inner product. -/
theorem covarianceOfIsCoerciveCLM_psd
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) (y : E) :
    0 ≤ inner ℝ y (covarianceOfIsCoerciveCLM A hc hA y) := by
  let x : E := covarianceOfIsCoerciveCLM A hc hA y
  have hAx : A x = y := by
    dsimp [x]
    exact precision_apply_covarianceOfIsCoerciveCLM A hc hA y
  calc
    0 ≤ c * ‖x‖ ^ 2 := mul_nonneg hc.le (sq_nonneg ‖x‖)
    _ ≤ inner ℝ x (A x) := hA x
    _ = inner ℝ (A x) x := real_inner_comm _ _
    _ = inner ℝ y (covarianceOfIsCoerciveCLM A hc hA y) := by
      rw [hAx]

end YangMills.RG
