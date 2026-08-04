/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.FinitePiLpTypedCutoff
import YangMills.RG.FinitePiLpTypedWeightedRowKernel

/-!
# Weighted rows for finite-range scalar commutators

PRE-VALIDATION: this source is present, but its `.olean` has not yet been
materialized and its result is not compiler-verified.

The point of this estimate is quantitative.  If `K` already has a normalized
weighted-row budget, the commutator `[h,K]` pays only the Lipschitz variation
of `h` across the finite range of `K`.  It does not reconstruct that row budget
from a pointwise kernel estimate and a range-ball cardinality.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

/-- A contractive diagonal multiplier on the source side preserves a
weighted-row estimate at the same rate and amplitude. -/
theorem finitePiLpTypedWeightedRowKernelBound_comp_scalarMultiplier_right
    {ι κ g : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (h : ι → ℝ) (T : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    {dist : κ → ι → ℕ} {A rate : ℝ}
    (hh : ∀ source, ‖h source‖ ≤ 1)
    (hT : FinitePiLpTypedWeightedRowKernelBound T dist A rate) :
    FinitePiLpTypedWeightedRowKernelBound
      (T.comp (finitePiLpScalarMultiplier (g := g) h)) dist A rate := by
  refine ⟨hT.1, hT.2.1, ?_⟩
  intro source v
  rw [ContinuousLinearMap.comp_apply,
    finitePiLpScalarMultiplier_single]
  calc
    ∑ target : κ,
          Real.exp (rate * (dist target source : ℝ)) *
            ‖T (singleFinitePiLp source (h source • v)) target‖
        ≤ A * ‖h source • v‖ := hT.2.2 source (h source • v)
    _ = A * (‖h source‖ * ‖v‖) := by rw [norm_smul]
    _ ≤ A * (1 * ‖v‖) := by
      apply mul_le_mul_of_nonneg_left _ hT.1
      exact mul_le_mul_of_nonneg_right (hh source) (norm_nonneg v)
    _ = A * ‖v‖ := by ring

/-- A scalar commutator against a finite-range operator preserves an existing
weighted-row estimate and pays exactly `slope * range`.  In particular, no
cardinality of a range ball is introduced here. -/
theorem finitePiLpTypedWeightedRowKernelBound_scalarCommutator
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (h : ι → ℝ)
    (K : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g)
    (dist : ι → ι → ℕ) (range : ℕ) {slope A rate : ℝ}
    (hslope : 0 ≤ slope)
    (hfinite : FinitePiLpTypedFiniteRange K dist range)
    (hLipschitz : ∀ target source,
      ‖h target - h source‖ ≤ slope * (dist target source : ℝ))
    (hK : FinitePiLpTypedWeightedRowKernelBound K dist A rate) :
    FinitePiLpTypedWeightedRowKernelBound
      ((finitePiLpScalarMultiplier (g := g) h).comp K -
        K.comp (finitePiLpScalarMultiplier (g := g) h))
      dist (slope * (range : ℝ) * A) rate := by
  refine ⟨mul_nonneg (mul_nonneg hslope (Nat.cast_nonneg range)) hK.1,
    hK.2.1, ?_⟩
  intro source v
  have hpoint : ∀ target : ι,
      Real.exp (rate * (dist target source : ℝ)) *
          ‖((finitePiLpScalarMultiplier (g := g) h).comp K -
              K.comp (finitePiLpScalarMultiplier (g := g) h))
              (singleFinitePiLp source v) target‖
        ≤ (slope * (range : ℝ)) *
            (Real.exp (rate * (dist target source : ℝ)) *
              ‖K (singleFinitePiLp source v) target‖) := by
    intro target
    have hcomm :
        ((finitePiLpScalarMultiplier (g := g) h).comp K -
            K.comp (finitePiLpScalarMultiplier (g := g) h))
            (singleFinitePiLp source v) target =
          (h target - h source) •
            K (singleFinitePiLp source v) target := by
      rw [ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.comp_apply]
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
    ∑ target : ι,
          Real.exp (rate * (dist target source : ℝ)) *
            ‖((finitePiLpScalarMultiplier (g := g) h).comp K -
                K.comp (finitePiLpScalarMultiplier (g := g) h))
                (singleFinitePiLp source v) target‖
        ≤ ∑ target : ι, (slope * (range : ℝ)) *
            (Real.exp (rate * (dist target source : ℝ)) *
              ‖K (singleFinitePiLp source v) target‖) := by
          exact Finset.sum_le_sum fun target _ => hpoint target
    _ = (slope * (range : ℝ)) *
          ∑ target : ι,
            Real.exp (rate * (dist target source : ℝ)) *
              ‖K (singleFinitePiLp source v) target‖ := by
          rw [Finset.mul_sum]
    _ ≤ (slope * (range : ℝ)) * (A * ‖v‖) := by
          exact mul_le_mul_of_nonneg_left (hK.2.2 source v)
            (mul_nonneg hslope (Nat.cast_nonneg range))
    _ = (slope * (range : ℝ) * A) * ‖v‖ := by ring

end

end YangMills.RG
