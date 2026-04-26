/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Klarner bound statement (Phase 316)

The Klarner bound on lattice animal counts.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L33_CreativeAttack_KlarnerBFSBound

/-! ## §1. The Klarner bound -/

/-- **Klarner bound** (statement): there exist constants `K, α > 0`
    such that for every `n ≥ 1`, the number of lattice animals in
    `Z^d` of size `n` is at most `K · α^n`.

    The BFS-tree argument gives `α ≤ 2d - 1`. -/
def KlarnerBound (d : ℕ) (a : ℕ → ℕ) : Prop :=
  ∃ K α : ℝ, 0 < K ∧ 0 < α ∧ ∀ n : ℕ, 1 ≤ n → (a n : ℝ) ≤ K * α ^ n

/-! ## §2. Klarner with explicit α = 2d-1 -/

/-- **Klarner bound with α = 2d-1** (explicit BFS bound). -/
def KlarnerBound_BFS (d : ℕ) (a : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → (a n : ℝ) ≤ ((2 * d - 1 : ℕ) : ℝ) ^ n

/-- **BFS Klarner bound implies general Klarner bound** (with
    `K = 1, α = 2d-1`). -/
theorem KlarnerBound_BFS_implies_general (d : ℕ) (a : ℕ → ℕ)
    (hd : 1 ≤ d) (h_BFS : KlarnerBound_BFS d a) :
    KlarnerBound d a := by
  refine ⟨1, ((2 * d - 1 : ℕ) : ℝ), by norm_num, ?_, ?_⟩
  · have h2d : (2 * d : ℕ) ≥ 2 := by omega
    have : (2 * d - 1 : ℕ) ≥ 1 := by omega
    have : ((2 * d - 1 : ℕ) : ℝ) ≥ 1 := by exact_mod_cast this
    linarith
  · intro n hn
    have h_BFS_n := h_BFS n hn
    linarith

#print axioms KlarnerBound_BFS_implies_general

end YangMills.L33_CreativeAttack_KlarnerBFSBound
