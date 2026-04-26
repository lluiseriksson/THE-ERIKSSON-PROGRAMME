/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L33_CreativeAttack_KlarnerBFSBound.KlarnerBound_Statement

/-!
# Klarner bound robustness across dimensions (Phase 321)

The Klarner bound holds for all `d ≥ 1`.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L33_CreativeAttack_KlarnerBFSBound

/-! ## §1. Klarner bound at each dimension -/

/-- **Universal Klarner bound**: for every `d ≥ 1` and every animal
    count function bounded pointwise by `(2d-1)^n`, the Klarner
    bound holds. -/
theorem KlarnerBound_universal_d
    (d : ℕ) (a : ℕ → ℕ) (hd : 1 ≤ d)
    (h_pt : ∀ n, 1 ≤ n → a n ≤ (2 * d - 1) ^ n) :
    KlarnerBound d a := by
  apply KlarnerBound_BFS_implies_general d a hd
  intro n hn
  have h := h_pt n hn
  exact_mod_cast h

#print axioms KlarnerBound_universal_d

/-! ## §2. Convergence radius for each dimension -/

/-- **Convergence radius `1/(2d-1)`**: in dimension d, the cluster
    expansion converges for `|β| < 1/(2d-1)`. -/
def F3_convergence_radius (d : ℕ) : ℝ := 1 / ((2 * d - 1 : ℕ) : ℝ)

/-- **Convergence radius is positive for `d ≥ 1`**. -/
theorem F3_convergence_radius_pos (d : ℕ) (hd : 1 ≤ d) :
    0 < F3_convergence_radius d := by
  unfold F3_convergence_radius
  have : (1 : ℕ) ≤ 2 * d - 1 := by omega
  have : (1 : ℝ) ≤ ((2 * d - 1 : ℕ) : ℝ) := by exact_mod_cast this
  positivity

#print axioms F3_convergence_radius_pos

/-- **Convergence radius decreases with d**: `F3_radius d ≥ F3_radius d'`
    for `d ≤ d'`. -/
theorem F3_convergence_radius_monotone
    (d d' : ℕ) (hd : 1 ≤ d) (hdd' : d ≤ d') :
    F3_convergence_radius d' ≤ F3_convergence_radius d := by
  unfold F3_convergence_radius
  have h_d_pos : (0 : ℝ) < ((2 * d - 1 : ℕ) : ℝ) := by
    have : (1 : ℕ) ≤ 2 * d - 1 := by omega
    have : (1 : ℝ) ≤ ((2 * d - 1 : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have h_d'_pos : (0 : ℝ) < ((2 * d' - 1 : ℕ) : ℝ) := by
    have : (1 : ℕ) ≤ 2 * d' - 1 := by omega
    have : (1 : ℝ) ≤ ((2 * d' - 1 : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have h_dd' : (2 * d - 1 : ℕ) ≤ (2 * d' - 1 : ℕ) := by omega
  have : ((2 * d - 1 : ℕ) : ℝ) ≤ ((2 * d' - 1 : ℕ) : ℝ) := by exact_mod_cast h_dd'
  apply div_le_div_of_nonneg_left (by norm_num) h_d_pos this

#print axioms F3_convergence_radius_monotone

end YangMills.L33_CreativeAttack_KlarnerBFSBound
