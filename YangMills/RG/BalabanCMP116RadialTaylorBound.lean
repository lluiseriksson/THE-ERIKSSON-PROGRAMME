import YangMills.RG.BalabanCMP116Eq142SourceSplit
import YangMills.RG.BalabanCMP116Eq143To219
import YangMills.RG.PhysicalGramKernel

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

/-- A bilinear estimate on single-bond probes produces the corresponding
source-facing block-kernel estimate without a basis expansion or a
Lie-dimension loss.  The proof tests the output block against itself and
cancels its norm. -/
theorem physicalCovarianceExponentialKernelBound_of_probe_inner
    {d N Nc : ℕ} [NeZero N]
    (C :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (A κ : ℝ)
    (hA : 0 ≤ A) (hκ : 0 < κ)
    (hprobe : ∀ source target (v w : SUNLieCoord Nc),
      |inner ℝ
          (singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) target w)
          (C (singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) source v))| ≤
        A * Real.exp (-(κ * (dist target source : ℝ))) * ‖v‖ * ‖w‖) :
    PhysicalCovarianceExponentialKernelBound C dist A κ := by
  refine ⟨hA, hκ, ?_⟩
  intro source target v
  let y :=
    C (singlePhysicalBondCochain
      (d := d) (N := N) (Nc := Nc) source v) target
  have hinner :
      inner ℝ
          (singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) target y)
          (C (singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) source v)) =
        inner ℝ y y := by
    rw [real_inner_comm, inner_singlePhysicalBondCochain_right]
  have hsq :
      ‖y‖ ^ 2 ≤
        (A * Real.exp (-(κ * (dist target source : ℝ))) * ‖v‖) * ‖y‖ := by
    calc
      ‖y‖ ^ 2 = inner ℝ y y := (real_inner_self_eq_norm_sq y).symm
      _ ≤ |inner ℝ y y| := le_abs_self _
      _ =
          |inner ℝ
            (singlePhysicalBondCochain
              (d := d) (N := N) (Nc := Nc) target y)
            (C (singlePhysicalBondCochain
              (d := d) (N := N) (Nc := Nc) source v))| := by
            rw [hinner]
      _ ≤
          A * Real.exp (-(κ * (dist target source : ℝ))) *
            ‖v‖ * ‖y‖ :=
        hprobe source target v y
  change ‖y‖ ≤
    A * Real.exp (-(κ * (dist target source : ℝ))) * ‖v‖
  rcases eq_or_lt_of_le (norm_nonneg y) with hy | hy
  · rw [← hy]
    positivity
  · nlinarith

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

/-- Source-facing kernel producer for the equation-(1.42) operator.

Unlike a field of type `PhysicalCovarianceExponentialKernelBound`, the input
is the literal Hessian estimate for `V_k(Y, ·) - V''_k(Y, ·)` along the radial
segment.  The radial Taylor theorem preserves the estimate, and the
single-bond probe theorem converts its bilinear form to a block-kernel norm
without summing Lie coordinates. -/
theorem
    physicalCovarianceExponentialKernelBound_cmp116Eq142PhysicalSourceQuadratic_of_hessian
    {Y : Type*} {d N Nc : ℕ} [NeZero N]
    (total residual : Y → PhysicalGaugeOneCochain d N Nc → ℝ)
    (hsmooth : ∀ y, ContDiff ℝ 2
      (cmp116Eq142PhysicalQuadraticCore total residual y))
    (y : Y) (B : PhysicalGaugeOneCochain d N Nc)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (A κ : ℝ)
    (hA : 0 ≤ A) (hκ : 0 < κ)
    (hhess : ∀ source target (v w : SUNLieCoord Nc),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |cmp116FDerivHessian
          (cmp116Eq142PhysicalQuadraticCore total residual y)
          (t • B)
          (singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) source v)
          (singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) target w)| ≤
          A * Real.exp (-(κ * (dist target source : ℝ))) * ‖v‖ * ‖w‖) :
    PhysicalCovarianceExponentialKernelBound
      (cmp116Eq142PhysicalSourceQuadratic total residual hsmooth y B)
      dist A κ := by
  apply physicalCovarianceExponentialKernelBound_of_probe_inner
    (cmp116Eq142PhysicalSourceQuadratic total residual hsmooth y B)
    dist A κ hA hκ
  intro source target v w
  exact
    abs_inner_cmp116Eq142PhysicalSourceQuadratic_le_of_hessian
      total residual hsmooth y B
      (singlePhysicalBondCochain
        (d := d) (N := N) (Nc := Nc) target w)
      (singlePhysicalBondCochain
        (d := d) (N := N) (Nc := Nc) source v)
      (A * Real.exp (-(κ * (dist target source : ℝ))) * ‖v‖ * ‖w‖)
      (hhess source target v w)

end

end YangMills.RG
