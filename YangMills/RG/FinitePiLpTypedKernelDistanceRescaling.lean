import YangMills.RG.FinitePiLpTypedKernel

/-!
PRE-VALIDATION: source present; its `.olean` is not yet materialized and the result is not compiler-verified.

# Exact distance rescaling for rectangular exponential kernels

If a coarse distance satisfies

`ell * coarseDist <= fineDist + boundary`,

then fine-distance decay at rate `rate` gives coarse-distance decay at rate
`ell * rate`.  The block-boundary loss stays visible as the single amplitude
factor `exp (rate * boundary)`.

This is only the algebraic distance bridge.  It does not construct a C6d
Green, any of the four CMP99 (3.42) actions, uniform `B0`/`delta0`, window 15,
or a terminal `TermSource` field.
-/

namespace YangMills.RG

noncomputable section

/-- Rescale a rectangular exponential kernel estimate through an inverse
metric comparison, retaining the exact boundary payment. -/
theorem finitePiLpTypedExponentialKernelBound_rescale_dist
    {ι κ g : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    {C : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g}
    {fineDist coarseDist : κ → ι → ℕ}
    {A rate : ℝ} {ell boundary : ℕ}
    (hell : 0 < ell)
    (hmetric : ∀ target source,
      ell * coarseDist target source ≤ fineDist target source + boundary)
    (hC : FinitePiLpTypedExponentialKernelBound C fineDist A rate) :
    FinitePiLpTypedExponentialKernelBound C coarseDist
      (A * Real.exp (rate * (boundary : ℝ))) ((ell : ℝ) * rate) := by
  have hellReal : 0 < (ell : ℝ) := by exact_mod_cast hell
  refine ⟨mul_nonneg hC.1 (Real.exp_pos _).le,
    mul_pos hellReal hC.2.1, ?_⟩
  intro source target v
  let df : ℝ := fineDist target source
  let dc : ℝ := coarseDist target source
  let b : ℝ := boundary
  have hmetricReal : (ell : ℝ) * dc ≤ df + b := by
    dsimp [df, dc, b]
    exact_mod_cast hmetric target source
  have hmetricScaled :=
    mul_le_mul_of_nonneg_left hmetricReal hC.2.1.le
  have hexponent :
      -(rate * df) ≤ rate * b - ((ell : ℝ) * rate) * dc := by
    nlinarith [hmetricScaled]
  have hexp :
      Real.exp (-(rate * df)) ≤
        Real.exp (rate * b - ((ell : ℝ) * rate) * dc) :=
    Real.exp_le_exp.mpr hexponent
  calc
    ‖C (singleFinitePiLp source v) target‖ ≤
        A * Real.exp (-(rate * df)) * ‖v‖ := by
      simpa [df] using hC.2.2 source target v
    _ ≤ A * Real.exp (rate * b - ((ell : ℝ) * rate) * dc) * ‖v‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexp hC.1) (norm_nonneg v)
    _ = (A * Real.exp (rate * (boundary : ℝ))) *
        Real.exp (-(((ell : ℝ) * rate) *
          (coarseDist target source : ℝ))) * ‖v‖ := by
      have hsplit :
          Real.exp (rate * b - ((ell : ℝ) * rate) * dc) =
            Real.exp (rate * b) *
              Real.exp (-(((ell : ℝ) * rate) * dc)) := by
        rw [show rate * b - ((ell : ℝ) * rate) * dc =
          rate * b + (-(((ell : ℝ) * rate) * dc)) by ring,
          Real.exp_add]
      rw [hsplit]
      simp only [b, dc]
      ring

end

end YangMills.RG
