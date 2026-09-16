import YangMills.RG.BalabanCMP116RadialTaylor
import YangMills.RG.RealBilinearRiesz

open MeasureTheory Set
open scoped Interval

namespace YangMills.RG

noncomputable section

theorem testRadialHessian_intervalIntegrable
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

noncomputable def testRadialTaylorRightLinearMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (B A : E) (hf : ContDiff ℝ 2 f) : E →ₗ[ℝ] ℝ where
  toFun A' := 2 * ∫ t in (0 : ℝ)..1,
    (1 - t) * cmp116FDerivHessian f (t • B) A A'
  map_add' A₁ A₂ := by
    have h₁ := testRadialHessian_intervalIntegrable f B A A₁ hf
    have h₂ := testRadialHessian_intervalIntegrable f B A A₂ hf
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
    have h := testRadialHessian_intervalIntegrable f B A A' hf
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

noncomputable def testRadialTaylorOuterAlgebraicLinearMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (B : E) (hf : ContDiff ℝ 2 f) : E →ₗ[ℝ] (E →ₗ[ℝ] ℝ) where
  toFun A := testRadialTaylorRightLinearMap f B A hf
  map_add' A₁ A₂ := by
    ext A'
    change 2 * (∫ t in (0 : ℝ)..1,
      (1 - t) * cmp116FDerivHessian f (t • B) (A₁ + A₂) A') =
      2 * (∫ t in (0 : ℝ)..1,
        (1 - t) * cmp116FDerivHessian f (t • B) A₁ A') +
      2 * (∫ t in (0 : ℝ)..1,
        (1 - t) * cmp116FDerivHessian f (t • B) A₂ A')
    have h₁ := testRadialHessian_intervalIntegrable f B A₁ A' hf
    have h₂ := testRadialHessian_intervalIntegrable f B A₂ A' hf
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
    have h := testRadialHessian_intervalIntegrable f B A A' hf
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

noncomputable def testRadialTaylorOuterLinearMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E → ℝ) (B : E) (hf : ContDiff ℝ 2 f) : E →ₗ[ℝ] (E →L[ℝ] ℝ) :=
  (LinearMap.toContinuousLinearMap :
    (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).comp
      (testRadialTaylorOuterAlgebraicLinearMap f B hf)

noncomputable def testRadialTaylorBilinear
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E → ℝ) (B : E) (hf : ContDiff ℝ 2 f) : E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (testRadialTaylorOuterLinearMap f B hf)

theorem testRadialTaylorBilinear_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E → ℝ) (B A A' : E) (hf : ContDiff ℝ 2 f) :
    testRadialTaylorBilinear f B hf A A' =
      2 * ∫ t in (0 : ℝ)..1,
        (1 - t) * cmp116FDerivHessian f (t • B) A A' := rfl

noncomputable def testRadialTaylorOperator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (f : E → ℝ) (B : E) (hf : ContDiff ℝ 2 f) : E →L[ℝ] E :=
  realBilinearRiesz (testRadialTaylorBilinear f B hf)

theorem testRadialTaylorOperator_decomposition
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (f : E → ℝ) (B : E) (hf : ContDiff ℝ 2 f) :
    f B = f 0 + fderiv ℝ f 0 B +
      (1 / 2 : ℝ) * inner ℝ B (testRadialTaylorOperator f B hf B) := by
  have htaylor := cmp116TaylorIntegral_radial f B hf
  have hinner : inner ℝ B (testRadialTaylorOperator f B hf B) =
      testRadialTaylorBilinear f B hf B B := by
    rw [real_inner_comm]
    exact inner_realBilinearRiesz (testRadialTaylorBilinear f B hf) B B
  rw [hinner, testRadialTaylorBilinear_apply]
  linarith

end

end YangMills.RG
