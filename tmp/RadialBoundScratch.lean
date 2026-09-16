import YangMills.RG.BalabanCMP116Eq142SourceSplit

open MeasureTheory Set Filter
open scoped Interval RealInnerProductSpace

namespace YangMills.RG

noncomputable section

theorem testRadialOperator_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (f : E → ℝ) (B A A' : E) (hf : ContDiff ℝ 2 f)
    (C : ℝ) (hC : 0 ≤ C)
    (hhess : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |cmp116FDerivHessian f (t • B) A' A| ≤ C) :
    |inner ℝ A (cmp116RadialTaylorOperator f B hf A')| ≤ C := by
  rw [inner_cmp116RadialTaylorOperator]
  have hmajorInt : IntervalIntegrable (fun t : ℝ => (1 - t) * C) volume 0 1 :=
    ((continuous_const.sub continuous_id).mul continuous_const).intervalIntegrable 0 1
  have hnorm : ‖∫ t in (0 : ℝ)..1,
      (1 - t) * cmp116FDerivHessian f (t • B) A' A‖ ≤
      ∫ t in (0 : ℝ)..1, (1 - t) * C := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
      (Filter.Eventually.of_forall ?_) hmajorInt
    intro t ht
    have ht0 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ht0]
    exact mul_le_mul_of_nonneg_left (hhess t ⟨le_of_lt ht.1, ht.2⟩) ht0
  have hweight : (∫ t in (0 : ℝ)..1, (1 - t) * C) = C / 2 := by
    rw [intervalIntegral.integral_mul_const]
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ => s - s ^ 2 / 2) (1 - t) t := by
      intro t ht
      convert (hasDerivAt_id t).sub
        (((hasDerivAt_id t).pow 2).div_const 2) using 1 <;>
        simp only [id_eq] <;> ring
    have hint : IntervalIntegrable (fun t : ℝ => 1 - t) volume 0 1 :=
      (continuous_const.sub continuous_id).intervalIntegrable 0 1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    ring
  rw [hweight] at hnorm
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num
  calc
    2 * |∫ t in (0 : ℝ)..1,
        (1 - t) * cmp116FDerivHessian f (t • B) A' A| =
        2 * ‖∫ t in (0 : ℝ)..1,
          (1 - t) * cmp116FDerivHessian f (t • B) A' A‖ := by
            rw [Real.norm_eq_abs]
    _ ≤ 2 * (C / 2) := mul_le_mul_of_nonneg_left hnorm (by norm_num)
    _ = C := by ring

end

end YangMills.RG
