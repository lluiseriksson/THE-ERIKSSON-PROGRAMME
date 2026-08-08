/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.FinitePiLpBlockLocalizedSup

/-!
# Source-owner overlap sums for localized-action bounds

This module was compiler-verified at exact source checkpoint
`a814d95ac5bb20fa8bfe8871e8764caf2353153b` in cold GitHub Actions run
`31180210309`; its audited declaration uses exactly
`[propext, Classical.choice, Quot.sound]`.

The CMP99 (3.89) estimate acts on an arbitrary field supported in one complete
source-owner fibre.  A pointwise probe estimate is therefore not enough to
sum regional cells.  The theorem below first uses the exact decomposition of
the field into coordinate probes and the rightmost-cutoff vanishing identity
to remove every inactive cell.  Only then are the per-cell localized-action
bounds summed.

Consequently the amplitude pays the geometric source-owner overlap `N`, not
the total number of cells and not a numerical estimate on a probe expansion.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

/-- A family of source-owner localized-action estimates sums with its exact
owner overlap.  Inactive summands are eliminated algebraically on arbitrary
owner-supported fields before any norm estimate is taken. -/
theorem finitePiLpTypedBlockLocalizedSupBound_sum_of_sourceOwnerOverlap
    {ι κ β g n : Type*}
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Fintype κ] [Fintype n]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (term : n → FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    (active : n → β → Prop) [DecidableRel active]
    (sourceOwner : ι → β) (targetOwner : κ → β)
    (dist : β → β → ℕ) {N : ℕ} {A rate : ℝ}
    (hA : 0 ≤ A) (hrate : 0 < rate)
    (hoverlap : ∀ owner,
      (Finset.univ.filter fun i => active i owner).card ≤ N)
    (hsupport : ∀ i source (v : g), ¬ active i (sourceOwner source) →
      term i (singleFinitePiLp source v) = 0)
    (hterm : ∀ i,
      FinitePiLpTypedBlockLocalizedSupBound (term i)
        sourceOwner targetOwner dist A rate) :
    FinitePiLpTypedBlockLocalizedSupBound
      (∑ i, term i) sourceOwner targetOwner dist ((N : ℝ) * A) rate := by
  classical
  refine ⟨mul_nonneg (Nat.cast_nonneg N) hA, hrate, ?_⟩
  intro owner f hf target
  let supported : Finset n := Finset.univ.filter fun i => active i owner
  have hinactive : ∀ i, i ∉ supported → term i f = 0 := by
    intro i hi
    have hiOwner : ¬ active i owner := by
      simpa [supported] using hi
    have hdecomp :
        term i f =
          ∑ source, term i (singleFinitePiLp source (f source)) := by
      rw [← map_sum, sum_singleFinitePiLp_eq]
    rw [hdecomp]
    apply Finset.sum_eq_zero
    intro source _
    by_cases hsource : sourceOwner source = owner
    · apply hsupport i source (f source)
      simpa [hsource] using hiOwner
    · rw [hf source hsource]
      have hsingle : singleFinitePiLp source (0 : g) = 0 := by
        apply PiLp.ext
        intro target'
        by_cases htarget : target' = source
        · subst target'
          simp
        · rw [singleFinitePiLp_of_ne (0 : g) htarget]
          rfl
      rw [hsingle, map_zero]
  have hfamily :
      (∑ i, term i) f = ∑ i ∈ supported, term i f := by
    rw [ContinuousLinearMap.sum_apply]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hnot
    exact hinactive i (by simpa [supported] using hnot)
  rw [hfamily, WithLp.ofLp_sum, Finset.sum_apply]
  calc
    ‖∑ i ∈ supported, term i f target‖ ≤
        ∑ i ∈ supported, ‖term i f target‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ supported,
        A * Real.exp (-(rate * (dist (targetOwner target) owner : ℝ))) *
          finitePiLpSupNorm f := by
      apply Finset.sum_le_sum
      intro i _hi
      exact (hterm i).2.2 owner f hf target
    _ = (supported.card : ℝ) *
        (A * Real.exp (-(rate * (dist (targetOwner target) owner : ℝ))) *
          finitePiLpSupNorm f) := by
      simp
    _ ≤ (N : ℝ) *
        (A * Real.exp (-(rate * (dist (targetOwner target) owner : ℝ))) *
          finitePiLpSupNorm f) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hoverlap owner
      · exact mul_nonneg
          (mul_nonneg hA (Real.exp_pos _).le)
          (finitePiLpSupNorm_nonneg f)
    _ = ((N : ℝ) * A) *
        Real.exp (-(rate * (dist (targetOwner target) owner : ℝ))) *
          finitePiLpSupNorm f := by
      ring

end

end YangMills.RG
