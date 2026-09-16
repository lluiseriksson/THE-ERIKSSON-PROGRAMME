import YangMills.RG.FinitePiLpTypedKernel

namespace YangMills.RG
open scoped RealInnerProductSpace
noncomputable section

theorem test_inner_singleFinitePiLp_right
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    (f : FinitePiLpField ι g) (source : ι) (v : g) :
    inner ℝ f (singleFinitePiLp source v) = inner ℝ (f source) v := by
  classical
  rw [singleFinitePiLp_eq_toLp_single]
  rw [PiLp.inner_apply]
  rw [Finset.sum_eq_single source]
  · simp [Pi.single_apply]
  · intro x _ hx
    simp [Pi.single_apply, hx]
  · simp

theorem test_typedExponentialKernelBound_adjoint
    {ι κ g : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup g] [InnerProductSpace ℝ g] [CompleteSpace g]
    (dist : κ → ι → ℕ)
    {A rate : ℝ}
    (C : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    (hC : FinitePiLpTypedExponentialKernelBound C dist A rate) :
    FinitePiLpTypedExponentialKernelBound C.adjoint
      (fun target source => dist source target) A rate := by
  refine ⟨hC.1, hC.2.1, ?_⟩
  intro source target v
  let y := C.adjoint (singleFinitePiLp source v) target
  have hinner :
      inner ℝ y y = inner ℝ v
        (C (singleFinitePiLp target y) source) := by
    calc
      inner ℝ y y =
          inner ℝ (C.adjoint (singleFinitePiLp source v))
            (singleFinitePiLp target y) := by
        rw [test_inner_singleFinitePiLp_right]
      _ = inner ℝ (singleFinitePiLp source v)
          (C (singleFinitePiLp target y)) := by
        rw [ContinuousLinearMap.adjoint_inner_left]
      _ = inner ℝ v (C (singleFinitePiLp target y) source) := by
        rw [real_inner_comm, test_inner_singleFinitePiLp_right,
          real_inner_comm]
  have hblock := hC.2.2 target source y
  let coeff := A * Real.exp (-(rate * (dist source target : ℝ)))
  have hcoeff : 0 ≤ coeff := by
    exact mul_nonneg hC.1 (Real.exp_pos _).le
  have hsq : ‖y‖ ^ 2 ≤ (coeff * ‖v‖) * ‖y‖ := by
    calc
      ‖y‖ ^ 2 = inner ℝ y y := (real_inner_self_eq_norm_sq y).symm
      _ = inner ℝ v (C (singleFinitePiLp target y) source) := hinner
      _ ≤ ‖v‖ * ‖C (singleFinitePiLp target y) source‖ :=
        real_inner_le_norm _ _
      _ ≤ ‖v‖ * (coeff * ‖y‖) :=
        mul_le_mul_of_nonneg_left hblock (norm_nonneg v)
      _ = (coeff * ‖v‖) * ‖y‖ := by ring
  rcases eq_or_lt_of_le (norm_nonneg y) with hy0 | hy0
  · rw [← hy0]
    exact mul_nonneg hcoeff (norm_nonneg v)
  · have hcancel : ‖y‖ * ‖y‖ ≤ (coeff * ‖v‖) * ‖y‖ := by
      simpa [pow_two] using hsq
    exact le_of_mul_le_mul_right hcancel hy0

end
end YangMills.RG
