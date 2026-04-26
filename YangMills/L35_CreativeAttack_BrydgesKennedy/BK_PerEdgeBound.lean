/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Brydges-Kennedy per-edge bound (Phase 334)

The fundamental per-edge bound: `|exp(t) - 1| ≤ |t| · exp(|t|)`.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L35_CreativeAttack_BrydgesKennedy

/-! ## §1. The per-edge bound -/

/-- **Per-edge BK bound**: `|exp(t) - 1| ≤ |t| · exp(|t|)`.

    Proof: by FTC, `exp(t) - 1 = ∫₀ᵗ exp(s) ds`, so
    `|exp(t) - 1| ≤ |t| · max_{s ∈ [0,t]} |exp(s)| ≤ |t| · exp(|t|)`. -/
theorem BK_per_edge_bound (t : ℝ) :
    |Real.exp t - 1| ≤ |t| * Real.exp (|t|) := by
  -- Key step: |exp t - 1| = |∫₀ᵗ exp(s) ds| ≤ |t| · sup_s exp(s).
  -- For our purposes, the sup over [-|t|, |t|] is exp(|t|).
  -- We use Mathlib's `Real.abs_exp_sub_one_le` or similar.
  -- Alternative: split into cases t ≥ 0 vs t < 0.
  rcases le_or_lt 0 t with ht | ht
  · -- Case t ≥ 0: exp(t) ≥ 1, so exp(t) - 1 ≥ 0.
    have h_abs_t : |t| = t := abs_of_nonneg ht
    have h_exp_t_ge_1 : 1 ≤ Real.exp t := by
      rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
      exact Real.exp_le_exp.mpr ht
    have h_abs_diff : |Real.exp t - 1| = Real.exp t - 1 :=
      abs_of_nonneg (by linarith)
    rw [h_abs_diff, h_abs_t]
    -- Need: exp(t) - 1 ≤ t · exp(t).
    -- Equivalently: exp(t) ≤ 1 + t·exp(t) = 1 + t·exp(t).
    -- Or: exp(t)(1 - t) ≤ 1.
    -- By the inequality `1 + t ≤ exp(t)` (since exp is convex above its tangent),
    -- and `exp(t)(1 - t) ≤ 1` for `t ∈ [0, 1]`. For t > 1, RHS dominates.
    -- A cleaner bound: exp(t) - 1 = ∫₀ᵗ exp(s) ds ≤ t · exp(t) since exp(s) ≤ exp(t) for s ≤ t.
    -- We use the integral form via Mathlib: `Real.exp_sub_one_le_integral`
    -- or directly: `(exp t - 1) ≤ t · exp t` for t ≥ 0.
    nlinarith [Real.add_one_le_exp t, Real.exp_pos t]
  · -- Case t < 0.
    have h_abs_t : |t| = -t := abs_of_neg ht
    have h_exp_t_le_1 : Real.exp t < 1 := by
      rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
      exact Real.exp_lt_exp.mpr ht
    have h_abs_diff : |Real.exp t - 1| = 1 - Real.exp t :=
      abs_of_nonpos (by linarith) |>.trans (by ring)
    rw [h_abs_diff, h_abs_t]
    -- Need: 1 - exp(t) ≤ -t · exp(-t) = (-t)·exp(-t).
    -- Equivalently: 1 ≤ exp(t) + (-t)·exp(-t).
    -- We use: 1 - exp(t) ≤ -t (for t ≤ 0 from `1 + t ≤ exp(t)`),
    -- and -t = (-t)·1 ≤ (-t)·exp(-t) since exp(-t) ≥ 1 for -t ≥ 0.
    have h_neg_t_pos : 0 < -t := by linarith
    have h_exp_neg_t_ge_1 : 1 ≤ Real.exp (-t) := by
      rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
      exact Real.exp_le_exp.mpr (by linarith)
    have h_1_minus_exp : 1 - Real.exp t ≤ -t := by
      have := Real.add_one_le_exp t
      linarith
    have h_neg_t_le : -t ≤ -t * Real.exp (-t) := by
      have : (-t) * 1 ≤ (-t) * Real.exp (-t) :=
        mul_le_mul_of_nonneg_left h_exp_neg_t_ge_1 (le_of_lt h_neg_t_pos)
      linarith
    linarith

#print axioms BK_per_edge_bound

end YangMills.L35_CreativeAttack_BrydgesKennedy
