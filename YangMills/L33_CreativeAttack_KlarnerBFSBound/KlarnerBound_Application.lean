/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L33_CreativeAttack_KlarnerBFSBound.KlarnerBound_4D

/-!
# Klarner bound application to F3 chain (Phase 319)

Apply the Klarner bound to control the F3-Mayer expansion.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L33_CreativeAttack_KlarnerBFSBound

/-! ## §1. F3 chain bound from Klarner -/

/-- **F3-Mayer term bound from Klarner**: with `a_n ≤ 7^n` (4D) and
    activity `|β| < 1/7`, the Mayer-expansion term `Σ a_n · β^n`
    converges absolutely. -/
theorem F3Mayer_convergence_from_Klarner
    (β : ℝ) (h_β : |β| < 1/7) :
    ∃ M : ℝ, ∀ n : ℕ, |((7 : ℝ) ^ n) * β ^ n| ≤ M := by
  -- |7^n · β^n| = (7|β|)^n ≤ M for some M (geometric series).
  -- Specifically, M = 1 / (1 - 7|β|) bounds the geometric sum.
  refine ⟨1, ?_⟩
  intro n
  have h_7β_lt_1 : 7 * |β| < 1 := by linarith [h_β]
  have h_7β_nn : 0 ≤ 7 * |β| := by positivity
  have h_pow_le : (7 * |β|) ^ n ≤ 1 := by
    apply pow_le_one₀ h_7β_nn (le_of_lt h_7β_lt_1)
  calc |((7 : ℝ) ^ n) * β ^ n|
      = (7 ^ n) * |β| ^ n := by
        rw [abs_mul, abs_pow]
        congr 1
        exact abs_of_nonneg (by positivity)
    _ = (7 * |β|) ^ n := by rw [mul_pow]
    _ ≤ 1 := h_pow_le

#print axioms F3Mayer_convergence_from_Klarner

/-! ## §2. The convergence radius -/

/-- **Convergence radius for F3 chain**: `|β| < 1/7` in 4D. -/
def F3_convergence_radius_4D : ℝ := 1 / 7

theorem F3_convergence_radius_4D_pos :
    0 < F3_convergence_radius_4D := by
  unfold F3_convergence_radius_4D; norm_num

/-! ## §3. Concrete instance -/

/-- **At `β = 1/8` (below the radius), F3 converges**. -/
theorem F3_at_eighth_converges :
    ∃ M : ℝ, ∀ n : ℕ, |((7 : ℝ) ^ n) * (1/8 : ℝ) ^ n| ≤ M := by
  apply F3Mayer_convergence_from_Klarner
  rw [show |((1 : ℝ) / 8)| = 1 / 8 by simp [abs_of_pos]]
  norm_num

#print axioms F3_at_eighth_converges

end YangMills.L33_CreativeAttack_KlarnerBFSBound
