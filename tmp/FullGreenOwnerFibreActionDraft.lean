import YangMills.RG.FinitePiLpBlockLocalizedSup

/-!
# PRE-VALIDATION: one owner fibre, with its cardinality paid exactly once

Source is present; no `.olean` has been materialized for this draft and the
result is not compiler-verified. This is not a root import or a physical B0.

F5 generic action step: a point-source kernel estimate is weaker than an
arbitrary supported-field estimate. The conversion below pays the size of
that one owner fibre explicitly. Its physical specialization must prove the
R^4 count by the existing block-offset equivalence and consume the F4 R^-2
bound, leaving the printed R^2 value scale. No whole-torus count is allowed.
No regional inverse, derivative estimate or window15 follows here.
-/

namespace YangMills.RG

noncomputable section

/-- Point probes imply a supported-field bound only after paying the one
source fibre's explicit cardinality, with output/source orientation fixed. -/
theorem fullGreenOwnerFibreActionDraft
    {ι κ β g : Type*}
    [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype κ] [DecidableEq β]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (C : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    (sourceOwner : ι → β) (targetOwner : κ → β)
    (dist : β → β → ℕ) (N : ℕ) {A rate : ℝ}
    (hA : 0 ≤ A) (hrate : 0 < rate)
    (hfibre : ∀ owner,
      (Finset.univ.filter fun source => sourceOwner source = owner).card ≤ N)
    (hkernel : FinitePiLpTypedKernelBound C
      (fun target source =>
        A * Real.exp (-(rate * (dist (targetOwner target) (sourceOwner source) : ℝ))))) :
    FinitePiLpTypedBlockLocalizedSupBound C sourceOwner targetOwner dist
      ((N : ℝ) * A) rate := by
  classical
  refine ⟨mul_nonneg (Nat.cast_nonneg N) hA, hrate, ?_⟩
  intro owner f hf target
  let supported : Finset ι :=
    Finset.univ.filter fun source => sourceOwner source = owner
  have hinactive : ∀ source, source ∉ supported →
      C (singleFinitePiLp source (f source)) = 0 := by
    intro source hs
    have howner : sourceOwner source ≠ owner := by
      simpa [supported] using hs
    rw [hf source howner]
    have hsingle : singleFinitePiLp source (0 : g) = 0 := by
      apply PiLp.ext
      intro target'
      by_cases heq : target' = source
      · subst target'
        simp
      · rw [singleFinitePiLp_of_ne (0 : g) heq]
        rfl
    rw [hsingle, map_zero]
  have hdecomp : C f =
      ∑ source, C (singleFinitePiLp source (f source)) := by
    rw [← map_sum, sum_singleFinitePiLp_eq]
  have hfilter : (∑ source, C (singleFinitePiLp source (f source))) =
      ∑ source ∈ supported, C (singleFinitePiLp source (f source)) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro source _ hs
    exact hinactive source hs
  have happ : C f target =
      ∑ source ∈ supported, C (singleFinitePiLp source (f source)) target := by
    have h := congrArg (fun z : FinitePiLpField κ g => z target)
      (hdecomp.trans hfilter)
    simpa only [WithLp.ofLp_sum, Finset.sum_apply] using h
  rw [happ]
  calc
    ‖∑ source ∈ supported, C (singleFinitePiLp source (f source)) target‖ ≤
        ∑ source ∈ supported, ‖C (singleFinitePiLp source (f source)) target‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _source ∈ supported,
        A * Real.exp (-(rate * (dist (targetOwner target) owner : ℝ))) *
          finitePiLpSupNorm f := by
      apply Finset.sum_le_sum
      intro source hs
      have howner : sourceOwner source = owner := by
        simpa [supported] using hs
      have hk := hkernel source target (f source)
      rw [howner] at hk
      exact hk.trans (mul_le_mul_of_nonneg_left
        (norm_apply_le_finitePiLpSupNorm f source)
        (mul_nonneg hA (Real.exp_pos _).le))
    _ = (supported.card : ℝ) *
        (A * Real.exp (-(rate * (dist (targetOwner target) owner : ℝ))) *
          finitePiLpSupNorm f) := by simp
    _ ≤ (N : ℝ) *
        (A * Real.exp (-(rate * (dist (targetOwner target) owner : ℝ))) *
          finitePiLpSupNorm f) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hfibre owner
      · exact mul_nonneg (mul_nonneg hA (Real.exp_pos _).le)
          (finitePiLpSupNorm_nonneg f)
    _ = ((N : ℝ) * A) *
        Real.exp (-(rate * (dist (targetOwner target) owner : ℝ))) *
          finitePiLpSupNorm f := by ring

#print axioms fullGreenOwnerFibreActionDraft

end
end YangMills.RG
