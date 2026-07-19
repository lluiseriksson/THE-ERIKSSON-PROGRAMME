import YangMills.RG.BalabanCMP116Eq142SourceSplit
import YangMills.RG.BalabanCMP116Eq143To219

/-!
# No-loss bounds for the CMP116 radial Taylor operator

The source-faithful operator in equation (1.42) is twice the radial average
of the Hessian of `F_Y = V_k(Y, ·) - V''_k(Y, ·)`, with weight `1 - t`.
Since

`2 * integral t in 0..1, (1 - t) = 1`,

a uniform matrix-element bound for the Hessian along the radial segment
passes to `Q_F(B)` with exactly the same constant.  This file proves that
transfer, first on an arbitrary finite-dimensional real Hilbert space and
then for the physical CMP116 source split.

Honest scope: the bound along the radial segment remains an explicit
source-facing obligation.  In particular, this module does not assume or
manufacture the printed estimate (1.43); it proves that a physical Hessian
estimate of that size is sufficient to obtain (1.43) for the constructed
operator without any loss of constants.
-/

open MeasureTheory Set Filter
open scoped Interval RealInnerProductSpace

namespace YangMills.RG

noncomputable section

/-- A uniform matrix-element bound for the Hessian on the radial segment
passes to the radial Taylor operator with no loss. -/
theorem abs_inner_cmp116RadialTaylorOperator_le_of_hessian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (f : E → ℝ) (B A A' : E) (hf : ContDiff ℝ 2 f)
    (C : ℝ)
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
  calc
    2 * |∫ t in (0 : ℝ)..1,
        (1 - t) * cmp116FDerivHessian f (t • B) A' A| =
        2 * ‖∫ t in (0 : ℝ)..1,
          (1 - t) * cmp116FDerivHessian f (t • B) A' A‖ := by
            rw [Real.norm_eq_abs]
    _ ≤ 2 * (C / 2) := mul_le_mul_of_nonneg_left hnorm (by norm_num)
    _ = C := by ring

/-- Source-faithful specialization: a Hessian bound for
`V_k(Y, ·) - V''_k(Y, ·)` along `t B` is inherited, with the same constant,
by the physical operator constructed in equation (1.42). -/
theorem abs_inner_cmp116Eq142PhysicalSourceQuadratic_le_of_hessian
    {Y : Type*} {d N Nc : ℕ} [NeZero N]
    (total residual : Y → PhysicalGaugeOneCochain d N Nc → ℝ)
    (hsmooth : ∀ y, ContDiff ℝ 2
      (cmp116Eq142PhysicalQuadraticCore total residual y))
    (y : Y) (B A A' : PhysicalGaugeOneCochain d N Nc)
    (C : ℝ)
    (hhess : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |cmp116FDerivHessian
        (cmp116Eq142PhysicalQuadraticCore total residual y)
        (t • B) A' A| ≤ C) :
    |inner ℝ A
      (cmp116Eq142PhysicalSourceQuadratic total residual hsmooth y B A')| ≤ C := by
  exact abs_inner_cmp116RadialTaylorOperator_le_of_hessian
    (cmp116Eq142PhysicalQuadraticCore total residual y)
    B A A' (hsmooth y) C hhess

/-- Exact source-facing bridge to the printed majorant (1.43).  The theorem
does not assume a bound on `Q`: it assumes the corresponding bound on the
literal Hessian of `V_k - V''_k` along the radial segment, and produces (1.43)
for the internally constructed operator with the identical majorant. -/
theorem abs_inner_cmp116Eq142PhysicalSourceQuadratic_le_eq143QMajorant
    {Y : Type*} {d N Nc : ℕ} [NeZero N]
    (total residual : Y → PhysicalGaugeOneCochain d N Nc → ℝ)
    (hsmooth : ∀ y, ContDiff ℝ 2
      (cmp116Eq142PhysicalQuadraticCore total residual y))
    (y : Y) (B A A' : PhysicalGaugeOneCochain d N Nc)
    (C3 epsilon1 : ℝ) (M : ℕ) (C2 kappa1 domainDist : ℝ)
    (domainCard : ℕ)
    (hhess : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |cmp116FDerivHessian
        (cmp116Eq142PhysicalQuadraticCore total residual y)
        (t • B) A' A| ≤
          cmp116Eq143QMajorant C3 epsilon1 M C2 kappa1
            domainDist domainCard) :
    |inner ℝ A
      (cmp116Eq142PhysicalSourceQuadratic total residual hsmooth y B A')| ≤
        cmp116Eq143QMajorant C3 epsilon1 M C2 kappa1
          domainDist domainCard := by
  exact abs_inner_cmp116Eq142PhysicalSourceQuadratic_le_of_hessian
    total residual hsmooth y B A A'
    (cmp116Eq143QMajorant C3 epsilon1 M C2 kappa1 domainDist domainCard)
    hhess

end

end YangMills.RG
