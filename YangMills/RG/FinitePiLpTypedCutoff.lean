/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.FinitePiLpTypedKernel

/-!
# Diagonal cutoffs on finite typed PiLp fields

CMP99 Section C uses multiplication by the partition functions `h_Pi` and by
an exterior localization cutoff.  Consecutive regional fields have dependent
and generally different site types, so the cutoff algebra is recorded without
identifying their carriers.
-/

namespace YangMills.RG

noncomputable section

/-- Coordinatewise multiplication by a real scalar function. -/
noncomputable def finitePiLpScalarMultiplier
    {ι g : Type*} [Fintype ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (h : ι → ℝ) : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g :=
  LinearMap.toContinuousLinearMap
    { toFun := fun f => WithLp.toLp 2 fun x => h x • f x
      map_add' := fun f k => by
        apply PiLp.ext
        intro x
        exact smul_add _ _ _
      map_smul' := fun c f => by
        apply PiLp.ext
        intro x
        exact smul_comm _ c _ }

@[simp] theorem finitePiLpScalarMultiplier_apply
    {ι g : Type*} [Fintype ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (h : ι → ℝ) (f : FinitePiLpField ι g) (x : ι) :
    finitePiLpScalarMultiplier (g := g) h f x = h x • f x :=
  rfl

/-- A diagonal cutoff acts on a one-site probe only through the source value. -/
theorem finitePiLpScalarMultiplier_single
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (h : ι → ℝ) (source : ι) (v : g) :
    finitePiLpScalarMultiplier (g := g) h (singleFinitePiLp source v) =
      singleFinitePiLp source (h source • v) := by
  apply PiLp.ext
  intro target
  by_cases htarget : target = source
  · subst target
    simp
  · rw [finitePiLpScalarMultiplier_apply,
      singleFinitePiLp_of_ne v htarget,
      singleFinitePiLp_of_ne (h source • v) htarget]
    simp

/-- A contractive cutoff on the target side preserves an exponential kernel
certificate exactly. -/
theorem finitePiLpTypedExponentialKernelBound_comp_scalarMultiplier_left
    {ι κ g : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (h : κ → ℝ) (C : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    {dist : κ → ι → ℕ} {A rate : ℝ}
    (hh : ∀ target, ‖h target‖ ≤ 1)
    (hC : FinitePiLpTypedExponentialKernelBound C dist A rate) :
    FinitePiLpTypedExponentialKernelBound
      ((finitePiLpScalarMultiplier (g := g) h).comp C) dist A rate := by
  refine ⟨hC.1, hC.2.1, ?_⟩
  intro source target v
  rw [ContinuousLinearMap.comp_apply, finitePiLpScalarMultiplier_apply,
    norm_smul]
  calc
    ‖h target‖ * ‖C (singleFinitePiLp source v) target‖ ≤
        1 * ‖C (singleFinitePiLp source v) target‖ :=
      mul_le_mul_of_nonneg_right (hh target) (norm_nonneg _)
    _ = ‖C (singleFinitePiLp source v) target‖ := one_mul _
    _ ≤ A * Real.exp (-(rate * (dist target source : ℝ))) * ‖v‖ :=
      hC.2.2 source target v

/-- A contractive cutoff on the source side preserves an exponential kernel
certificate exactly. -/
theorem finitePiLpTypedExponentialKernelBound_comp_scalarMultiplier_right
    {ι κ g : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (h : ι → ℝ) (C : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    {dist : κ → ι → ℕ} {A rate : ℝ}
    (hh : ∀ source, ‖h source‖ ≤ 1)
    (hC : FinitePiLpTypedExponentialKernelBound C dist A rate) :
    FinitePiLpTypedExponentialKernelBound
      (C.comp (finitePiLpScalarMultiplier (g := g) h)) dist A rate := by
  refine ⟨hC.1, hC.2.1, ?_⟩
  intro source target v
  rw [ContinuousLinearMap.comp_apply,
    finitePiLpScalarMultiplier_single]
  calc
    ‖C (singleFinitePiLp source (h source • v)) target‖ ≤
        A * Real.exp (-(rate * (dist target source : ℝ))) * ‖h source • v‖ :=
      hC.2.2 source target (h source • v)
    _ = A * Real.exp (-(rate * (dist target source : ℝ))) *
        (‖h source‖ * ‖v‖) := by rw [norm_smul]
    _ ≤ A * Real.exp (-(rate * (dist target source : ℝ))) *
        (1 * ‖v‖) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hh source) (norm_nonneg v))
        (mul_nonneg hC.1 (Real.exp_pos _).le)
    _ = A * Real.exp (-(rate * (dist target source : ℝ))) * ‖v‖ := by ring

/-- Contractive cutoffs on both typed carriers preserve the same amplitude and
rate. -/
theorem finitePiLpTypedExponentialKernelBound_cut
    {ι κ g : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (hsource : ι → ℝ) (htarget : κ → ℝ)
    (C : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    {dist : κ → ι → ℕ} {A rate : ℝ}
    (hsource_le : ∀ source, ‖hsource source‖ ≤ 1)
    (htarget_le : ∀ target, ‖htarget target‖ ≤ 1)
    (hC : FinitePiLpTypedExponentialKernelBound C dist A rate) :
    FinitePiLpTypedExponentialKernelBound
      ((finitePiLpScalarMultiplier (g := g) htarget).comp
        (C.comp (finitePiLpScalarMultiplier (g := g) hsource))) dist A rate :=
  finitePiLpTypedExponentialKernelBound_comp_scalarMultiplier_left
    htarget _ htarget_le
    (finitePiLpTypedExponentialKernelBound_comp_scalarMultiplier_right
      hsource C hsource_le hC)

end

end YangMills.RG
