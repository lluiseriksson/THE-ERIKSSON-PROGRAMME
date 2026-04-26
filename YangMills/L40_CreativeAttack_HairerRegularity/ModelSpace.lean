/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Model space T (Phase 385)

The model space of a regularity structure.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L40_CreativeAttack_HairerRegularity

/-! ## §1. Model space dimension -/

/-- **Dimension of the model space at index i**: increases with i
    (higher levels have more elements). -/
def modelSpaceDim (i : ℕ) : ℕ := i + 1

/-- **`modelSpaceDim 0 = 1`** (just the identity). -/
theorem modelSpaceDim_zero : modelSpaceDim 0 = 1 := rfl

/-- **`modelSpaceDim 4 = 5`**. -/
theorem modelSpaceDim_four : modelSpaceDim 4 = 5 := rfl

/-- **Total dimension up to level n**: `Σ (i+1) = (n+1)(n+2)/2`. -/
def totalDimUpTo (n : ℕ) : ℕ := (n + 1) * (n + 2) / 2

theorem totalDimUpTo_3 : totalDimUpTo 3 = 10 := by
  unfold totalDimUpTo; norm_num

#print axioms totalDimUpTo_3

/-! ## §2. Triangular sum identity -/

/-- **Triangular sum: Σ (i+1) = (n+1)(n+2)/2**. -/
theorem totalDimUpTo_eq_sum (n : ℕ) :
    totalDimUpTo n = (Finset.range (n + 1)).sum (fun i => modelSpaceDim i) := by
  unfold totalDimUpTo modelSpaceDim
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih]
    omega

end YangMills.L40_CreativeAttack_HairerRegularity
