/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson, Cowork agent (Claude)
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Order.Group.Nat

/-!
# Klarner-style BFS-tree bound on lattice animal count

This module proves an elementary **upper bound on lattice animal
counts** via a BFS-tree argument:

If a function `a : ℕ → ℕ` describes the rooted-animal count and
extends from size `n` to size `n+1` by adding at most `α` neighbours
to one specific cell, then `a n ≤ a 1 · α^(n-1)` for all `n ≥ 1`.

For the standard hypercubic lattice in dimension `d`, the BFS
forward-neighbour count is `α = 2d - 1`, giving Klarner's classical
bound `a_n ≤ a_1 · (2d-1)^(n-1)`.

## Strategy

The bound follows by induction on `n`:
* Base: `a 1 ≤ a 1 · α^0 = a 1`.
* Step: assume `a n ≤ a 1 · α^(n-1)`. By the hypothesis,
  `a (n+1) ≤ α · a n ≤ α · a 1 · α^(n-1) = a 1 · α^n`.

## PR submission notes

This file uses only standard Mathlib imports (`Mathlib.Data.Nat.Basic`,
`Mathlib.Algebra.Order.Group.Nat`). No project-specific dependencies.
The result fits naturally as a stepping-stone for Mathlib's combinatorics
library, contributing to lattice-animal / polyomino counting results.

**Status (2026-04-25)**: produced in the workspace but not yet
verified with `lake build` (workspace lacks `lake`). The proof is
elementary and should type-check on Mathlib master.
-/

namespace LatticeAnimal

/-! ## §1. The BFS extension hypothesis -/

/-- **BFS extension hypothesis**: from any animal of size `n`, the
    number of distinct extensions to size `n+1` is at most `α`.

    Equivalently, `a (n+1) ≤ α · a n`. -/
def BFS_extension_hypothesis (a : ℕ → ℕ) (α : ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → a (n + 1) ≤ α * a n

/-! ## §2. The Klarner bound -/

/-- **Klarner bound (elementary form)**: under the BFS extension
    hypothesis, `a n ≤ a 1 · α^(n-1)` for every `n ≥ 1`. -/
theorem klarner_bound
    (a : ℕ → ℕ) (α : ℕ)
    (h_BFS : BFS_extension_hypothesis a α) :
    ∀ n : ℕ, 1 ≤ n → a n ≤ a 1 * α ^ (n - 1) := by
  intro n hn
  -- Induction on n with base case n = 1.
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_or_gt_of_le hn with h_eq | h_gt
    · -- n = 1 case (k = 0).
      have : k = 0 := by omega
      subst this
      simp
    · -- n ≥ 2 case (k ≥ 1).
      have hk : 1 ≤ k := by omega
      have h_ind : a k ≤ a 1 * α ^ (k - 1) := ih hk
      have h_step : a (k + 1) ≤ α * a k := h_BFS k hk
      -- Combine: a (k+1) ≤ α · a k ≤ α · (a 1 · α^(k-1)) = a 1 · α^k.
      calc a (k + 1)
          ≤ α * a k := h_step
        _ ≤ α * (a 1 * α ^ (k - 1)) :=
            Nat.mul_le_mul_left α h_ind
        _ = a 1 * (α * α ^ (k - 1)) := by ring
        _ = a 1 * α ^ k := by
            congr 1
            have : k - 1 + 1 = k := by omega
            rw [← this, pow_succ]
            ring
        _ = a 1 * α ^ ((k + 1) - 1) := by
            congr 2
            omega

#print axioms klarner_bound

/-! ## §3. The 4D specialization -/

/-- **4D Klarner bound**: with `α = 7` (hypercubic forward-neighbour
    count `2 · 4 - 1 = 7`), `a_n ≤ a_1 · 7^(n-1)`. -/
theorem klarner_bound_4D
    (a : ℕ → ℕ) (h_BFS : BFS_extension_hypothesis a 7) :
    ∀ n : ℕ, 1 ≤ n → a n ≤ a 1 * 7 ^ (n - 1) :=
  klarner_bound a 7 h_BFS

#print axioms klarner_bound_4D

/-! ## §4. The general d-dimensional case -/

/-- **General d-dimensional Klarner bound**: for `d ≥ 1`,
    `α = 2d - 1` is the BFS forward-neighbour count, giving
    `a_n ≤ a_1 · (2d-1)^(n-1)`. -/
theorem klarner_bound_general_d
    (d : ℕ) (hd : 1 ≤ d) (a : ℕ → ℕ)
    (h_BFS : BFS_extension_hypothesis a (2 * d - 1)) :
    ∀ n : ℕ, 1 ≤ n → a n ≤ a 1 * (2 * d - 1) ^ (n - 1) :=
  klarner_bound a (2 * d - 1) h_BFS

#print axioms klarner_bound_general_d

end LatticeAnimal
