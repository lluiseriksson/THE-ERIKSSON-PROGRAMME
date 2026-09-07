import YangMills.RG.BalabanCMP116RadialTaylor
import YangMills.RG.RealBilinearRiesz

/-!
# Operator-valued radial Taylor average for CMP116

This file turns the scalar radial Taylor remainder into the continuous
bilinear form

`2 * integral t in 0..1, (1-t) D^2 f(tB)[A,A']`

on a finite-dimensional real field space.  Riesz representation then defines
the field-dependent operator `cmp116RadialTaylorOperator f B hf`, characterized
by

`<A, Q_f(B) A'> = 2 * integral t in 0..1, (1-t) D^2 f(tB)[A,A']`.

Consequently, when `f(0)=Df(0)=0`, the exact source normalization is

`f(B) = (1/2) <B, Q_f(B) B>`.

The construction is an integral average along the radial segment and is not
the pointwise Hessian at `B`.
-/

open MeasureTheory Set
open scoped Interval

namespace YangMills.RG

noncomputable section

theorem cmp116RadialHessian_intervalIntegrable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (B A A' : E) (hf : ContDiff ℝ 2 f) :
    IntervalIntegrable
      (fun t : ℝ => (1 - t) * cmp116FDerivHessian f (t • B) A A')
      volume 0 1 := by
  have hlineContinuous : Continuous (fun t : ℝ => t • B) :=
    continuous_id.smul continuous_const
  have hfderivCont : ContDiff ℝ 1 (fderiv ℝ f) :=
    hf.fderiv_right (by norm_num)
  have hhessCont : ContDiff ℝ 0 (fderiv ℝ (fderiv ℝ f)) :=
    hfderivCont.fderiv_right (by norm_num)
  have hscalar : Continuous (fun t : ℝ => (1 - t)) :=
    continuous_const.sub continuous_id
  exact (hscalar.mul
    (((hhessCont.continuous.clm_apply continuous_const).clm_apply continuous_const).comp
      hlineContinuous)).intervalIntegrable 0 1

/-- The radial Hessian average, algebraically linear in its second direction. -/
noncomputable def cmp116RadialTaylorRightLinearMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (B A : E) (hf : ContDiff ℝ 2 f) : E →ₗ[ℝ] ℝ where
  toFun A' := 2 * ∫ t in (0 : ℝ)..1,
    (1 - t) * cmp116FDerivHessian f (t • B) A A'
  map_add' A₁ A₂ := by
    have h₁ := cmp116RadialHessian_intervalIntegrable f B A A₁ hf
    have h₂ := cmp116RadialHessian_intervalIntegrable f B A A₂ hf
    have heq : (fun t : ℝ =>
        (1 - t) * cmp116FDerivHessian f (t • B) A (A₁ + A₂)) =
        fun t : ℝ =>
          (1 - t) * cmp116FDerivHessian f (t • B) A A₁ +
          (1 - t) * cmp116FDerivHessian f (t • B) A A₂ := by
      funext t
      rw [map_add]
      ring
    rw [heq, intervalIntegral.integral_add h₁ h₂]
    ring
  map_smul' c A' := by
    have h := cmp116RadialHessian_intervalIntegrable f B A A' hf
    have heq : (fun t : ℝ =>
        (1 - t) * cmp116FDerivHessian f (t • B) A (c • A')) =
        fun t : ℝ => c *
          ((1 - t) * cmp116FDerivHessian f (t • B) A A') := by
      funext t
      rw [map_smul]
      simp
      ring
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [heq, intervalIntegral.integral_const_mul]
    ring

/-- The same average as a bilinear map before continuity is bundled. -/
noncomputable def cmp116RadialTaylorOuterAlgebraicLinearMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (B : E) (hf : ContDiff ℝ 2 f) : E →ₗ[ℝ] (E →ₗ[ℝ] ℝ) where
  toFun A := cmp116RadialTaylorRightLinearMap f B A hf
  map_add' A₁ A₂ := by
    ext A'
    change 2 * (∫ t in (0 : ℝ)..1,
      (1 - t) * cmp116FDerivHessian f (t • B) (A₁ + A₂) A') =
      2 * (∫ t in (0 : ℝ)..1,
        (1 - t) * cmp116FDerivHessian f (t • B) A₁ A') +
      2 * (∫ t in (0 : ℝ)..1,
        (1 - t) * cmp116FDerivHessian f (t • B) A₂ A')
    have h₁ := cmp116RadialHessian_intervalIntegrable f B A₁ A' hf
    have h₂ := cmp116RadialHessian_intervalIntegrable f B A₂ A' hf
    have heq : (fun t : ℝ =>
        (1 - t) * cmp116FDerivHessian f (t • B) (A₁ + A₂) A') =
        fun t : ℝ =>
          (1 - t) * cmp116FDerivHessian f (t • B) A₁ A' +
          (1 - t) * cmp116FDerivHessian f (t • B) A₂ A' := by
      funext t
      simp only [map_add, ContinuousLinearMap.add_apply]
      ring
    rw [heq, intervalIntegral.integral_add h₁ h₂]
    ring
  map_smul' c A := by
    ext A'
    change 2 * (∫ t in (0 : ℝ)..1,
      (1 - t) * cmp116FDerivHessian f (t • B) (c • A) A') =
      c * (2 * (∫ t in (0 : ℝ)..1,
        (1 - t) * cmp116FDerivHessian f (t • B) A A'))
    have h := cmp116RadialHessian_intervalIntegrable f B A A' hf
    have heq : (fun t : ℝ =>
        (1 - t) * cmp116FDerivHessian f (t • B) (c • A) A') =
        fun t : ℝ => c *
          ((1 - t) * cmp116FDerivHessian f (t • B) A A') := by
      funext t
      rw [map_smul]
      simp
      ring
    rw [heq, intervalIntegral.integral_const_mul]
    ring

/-- Continuity in the second direction, obtained automatically in finite
dimension. -/
noncomputable def cmp116RadialTaylorOuterLinearMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E → ℝ) (B : E) (hf : ContDiff ℝ 2 f) : E →ₗ[ℝ] (E →L[ℝ] ℝ) :=
  (LinearMap.toContinuousLinearMap :
    (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).comp
      (cmp116RadialTaylorOuterAlgebraicLinearMap f B hf)

/-- Continuous bilinear radial Hessian average. -/
noncomputable def cmp116RadialTaylorBilinear
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E → ℝ) (B : E) (hf : ContDiff ℝ 2 f) : E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (cmp116RadialTaylorOuterLinearMap f B hf)

theorem cmp116RadialTaylorBilinear_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E → ℝ) (B A A' : E) (hf : ContDiff ℝ 2 f) :
    cmp116RadialTaylorBilinear f B hf A A' =
      2 * ∫ t in (0 : ℝ)..1,
        (1 - t) * cmp116FDerivHessian f (t • B) A A' := rfl

/-- The field-dependent CMP116 quadratic operator obtained by Riesz
representation of the radial Hessian average. -/
noncomputable def cmp116RadialTaylorOperator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (f : E → ℝ) (B : E) (hf : ContDiff ℝ 2 f) : E →L[ℝ] E :=
  realBilinearRiesz (cmp116RadialTaylorBilinear f B hf)

/-- Exact matrix-element characterization of the radial Taylor operator. -/
theorem inner_cmp116RadialTaylorOperator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (f : E → ℝ) (B A A' : E) (hf : ContDiff ℝ 2 f) :
    inner ℝ A (cmp116RadialTaylorOperator f B hf A') =
      2 * ∫ t in (0 : ℝ)..1,
        (1 - t) * cmp116FDerivHessian f (t • B) A' A := by
  rw [real_inner_comm]
  exact (inner_realBilinearRiesz
    (cmp116RadialTaylorBilinear f B hf) A' A).trans
      (cmp116RadialTaylorBilinear_apply f B A' A hf)

/-- The scalar quadratic value defined in the preceding module is exactly the
diagonal matrix element of the radial Taylor operator. -/
theorem cmp116RadialTaylorQuadratic_eq_inner_operator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (f : E → ℝ) (B : E) (hf : ContDiff ℝ 2 f) :
    cmp116RadialTaylorQuadratic f B =
      inner ℝ B (cmp116RadialTaylorOperator f B hf B) := by
  rw [inner_cmp116RadialTaylorOperator f B B B hf]
  rfl

/-- Exact equation-(1.42) decomposition, including the constant and linear
Taylor coefficients. -/
theorem cmp116RadialTaylorOperator_decomposition
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (f : E → ℝ) (B : E) (hf : ContDiff ℝ 2 f) :
    f B = f 0 + fderiv ℝ f 0 B +
      (1 / 2 : ℝ) * inner ℝ B (cmp116RadialTaylorOperator f B hf B) := by
  rw [← cmp116RadialTaylorQuadratic_eq_inner_operator f B hf]
  exact cmp116RadialTaylorQuadratic_decomposition f B hf

/-- Source-normalized equation-(1.42): the activity is exactly its
field-dependent radial quadratic term. -/
theorem cmp116RadialTaylorOperator_eq_of_normalized
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (f : E → ℝ) (B : E) (hf : ContDiff ℝ 2 f)
    (hf0 : f 0 = 0) (hdf0 : fderiv ℝ f 0 = 0) :
    f B = (1 / 2 : ℝ) *
      inner ℝ B (cmp116RadialTaylorOperator f B hf B) := by
  rw [← cmp116RadialTaylorQuadratic_eq_inner_operator f B hf]
  exact cmp116RadialTaylorQuadratic_eq_of_normalized f B hf hf0 hdf0

end

end YangMills.RG
