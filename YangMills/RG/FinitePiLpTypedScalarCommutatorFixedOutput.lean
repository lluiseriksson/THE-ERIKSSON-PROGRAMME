/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.FinitePiLpTypedCutoff
import YangMills.RG.FinitePiLpTypedFixedOutputWeightedKernel

/-!
# PRE-VALIDATION: fixed-output scalar-commutator bounds

The source of this module is present, but its `.olean` has not yet been
materialized and the result has not yet been verified by the Lean compiler.

CMP99 (3.88) fixes the output coordinate and sums over input coordinates.
This file estimates the scalar commutator directly in that orientation.  It
does not transport a source-fixed estimate through self-adjointness.  The
finite-range variation costs exactly `slope * range`, and the resulting
fixed-output sum yields a pointwise exponential kernel estimate term by term.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

/-- A scalar commutator preserves a fixed-output weighted estimate and pays
exactly the Lipschitz variation `slope * range`.  No range-ball cardinality
and no adjoint-orientation conversion enter this estimate. -/
theorem finitePiLpTypedFixedOutputWeightedKernelBound_scalarCommutator
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (h : ι → ℝ)
    (K : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g)
    (dist : ι → ι → ℕ) (range : ℕ) {slope A rate : ℝ}
    (hslope : 0 ≤ slope)
    (hfinite : FinitePiLpTypedFiniteRange K dist range)
    (hLipschitz : ∀ target source,
      ‖h target - h source‖ ≤ slope * (dist target source : ℝ))
    (hK : FinitePiLpTypedFixedOutputWeightedKernelBound K dist A rate) :
    FinitePiLpTypedFixedOutputWeightedKernelBound
      ((finitePiLpScalarMultiplier (g := g) h).comp K -
        K.comp (finitePiLpScalarMultiplier (g := g) h))
      dist (slope * (range : ℝ) * A) rate := by
  refine ⟨mul_nonneg (mul_nonneg hslope (Nat.cast_nonneg range)) hK.1,
    hK.2.1, ?_⟩
  intro target v
  have hpoint : ∀ source : ι,
      Real.exp (rate * (dist target source : ℝ)) *
          ‖((finitePiLpScalarMultiplier (g := g) h).comp K -
              K.comp (finitePiLpScalarMultiplier (g := g) h))
              (singleFinitePiLp source v) target‖
        ≤ (slope * (range : ℝ)) *
            (Real.exp (rate * (dist target source : ℝ)) *
              ‖K (singleFinitePiLp source v) target‖) := by
    intro source
    have hcomm :
        ((finitePiLpScalarMultiplier (g := g) h).comp K -
            K.comp (finitePiLpScalarMultiplier (g := g) h))
            (singleFinitePiLp source v) target =
          (h target - h source) •
            K (singleFinitePiLp source v) target := by
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
      change h target • K (singleFinitePiLp source v) target -
          K ((finitePiLpScalarMultiplier (g := g) h)
            (singleFinitePiLp source v)) target = _
      rw [finitePiLpScalarMultiplier_single]
      have hsingle : singleFinitePiLp source (h source • v) =
          h source • singleFinitePiLp source v := by
        apply PiLp.ext
        intro i
        by_cases hi : i = source
        · subst i
          simp
        · simp [singleFinitePiLp_of_ne, hi]
      rw [hsingle, map_smul, PiLp.smul_apply, sub_smul]
    rw [hcomm, norm_smul]
    by_cases hfar : range < dist target source
    · have hzero := hfinite source target v hfar
      rw [hzero, norm_zero, mul_zero, mul_zero]
      positivity
    · have hnear : (dist target source : ℝ) ≤ range := by
        exact_mod_cast Nat.le_of_not_gt hfar
      have hvariation : ‖h target - h source‖ ≤ slope * (range : ℝ) :=
        (hLipschitz target source).trans
          (mul_le_mul_of_nonneg_left hnear hslope)
      calc
        Real.exp (rate * (dist target source : ℝ)) *
              (‖h target - h source‖ *
                ‖K (singleFinitePiLp source v) target‖)
            ≤ Real.exp (rate * (dist target source : ℝ)) *
                ((slope * (range : ℝ)) *
                  ‖K (singleFinitePiLp source v) target‖) := by
              gcongr
        _ = (slope * (range : ℝ)) *
              (Real.exp (rate * (dist target source : ℝ)) *
                ‖K (singleFinitePiLp source v) target‖) := by ring
  calc
    ∑ source : ι,
          Real.exp (rate * (dist target source : ℝ)) *
            ‖((finitePiLpScalarMultiplier (g := g) h).comp K -
                K.comp (finitePiLpScalarMultiplier (g := g) h))
                (singleFinitePiLp source v) target‖
        ≤ ∑ source : ι, (slope * (range : ℝ)) *
            (Real.exp (rate * (dist target source : ℝ)) *
              ‖K (singleFinitePiLp source v) target‖) := by
          exact Finset.sum_le_sum fun source _ => hpoint source
    _ = (slope * (range : ℝ)) *
          ∑ source : ι,
            Real.exp (rate * (dist target source : ℝ)) *
              ‖K (singleFinitePiLp source v) target‖ := by
          rw [Finset.mul_sum]
    _ ≤ (slope * (range : ℝ)) * (A * ‖v‖) := by
          exact mul_le_mul_of_nonneg_left (hK.2.2 target v)
            (mul_nonneg hslope (Nat.cast_nonneg range))
    _ = (slope * (range : ℝ) * A) * ‖v‖ := by ring

/-- A fixed-output weighted sum contains every source term, so it yields the
pointwise exponential kernel estimate at the same amplitude and rate. -/
theorem finitePiLpTypedExponentialKernelBound_of_fixedOutputWeighted
    {ι κ g : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (T : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    (dist : κ → ι → ℕ) {A rate : ℝ}
    (hrate : 0 < rate)
    (hT : FinitePiLpTypedFixedOutputWeightedKernelBound T dist A rate) :
    FinitePiLpTypedExponentialKernelBound T dist A rate := by
  classical
  refine ⟨hT.1, hrate, ?_⟩
  intro source target v
  have hterm :
      Real.exp (rate * (dist target source : ℝ)) *
          ‖T (singleFinitePiLp source v) target‖ ≤
        ∑ next : ι,
          Real.exp (rate * (dist target next : ℝ)) *
            ‖T (singleFinitePiLp next v) target‖ := by
    exact Finset.single_le_sum
      (s := (Finset.univ : Finset ι))
      (f := fun next : ι =>
        Real.exp (rate * (dist target next : ℝ)) *
          ‖T (singleFinitePiLp next v) target‖)
      (fun next _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
      (Finset.mem_univ source)
  have hmul :
      Real.exp (rate * (dist target source : ℝ)) *
          ‖T (singleFinitePiLp source v) target‖ ≤ A * ‖v‖ :=
    hterm.trans (hT.2.2 target v)
  have hpos := Real.exp_pos (rate * (dist target source : ℝ))
  calc
    ‖T (singleFinitePiLp source v) target‖
        ≤ (A * ‖v‖) /
            Real.exp (rate * (dist target source : ℝ)) :=
      (le_div_iff₀ hpos).2 (by simpa [mul_comm] using hmul)
    _ = A * Real.exp (-(rate * (dist target source : ℝ))) * ‖v‖ := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
      ring

end

end YangMills.RG
