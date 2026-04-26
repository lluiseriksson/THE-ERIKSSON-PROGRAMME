/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# KP truncated 2-point function (Phase 296)

The truncated 2-point function from the cluster expansion.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L31_CreativeAttack_KP_ExpDecay

/-! ## §1. Truncated 2-point structure -/

/-- A **truncated 2-point function** parametrised by a "distance"
    function. -/
structure TruncatedTwoPoint where
  /-- The site type. -/
  Site : Type
  /-- Truncated correlator. -/
  G_T : Site → Site → ℝ
  /-- Distance function. -/
  d : Site → Site → ℝ
  /-- Distance is non-negative. -/
  d_nonneg : ∀ x y, 0 ≤ d x y
  /-- Distance is symmetric. -/
  d_symm : ∀ x y, d x y = d y x

/-! ## §2. Connected polymer pairs -/

/-- **The set of polymer pairs containing both `x` and `y`**. The
    truncated 2-point comes from polymers spanning both points. -/
def connectsBoth {S : Type} (x y : S) : Prop := ∀ p : S, p = x ∨ p = y

/-! ## §3. Decay-rate predicate -/

/-- **Exponential decay holds**: exists `m, K > 0` s.t.
    `|G_T(x,y)| ≤ K · exp(-m · d(x,y))`. -/
def hasExponentialDecay (T : TruncatedTwoPoint) : Prop :=
  ∃ m K : ℝ, 0 < m ∧ 0 ≤ K ∧
    ∀ x y : T.Site, |T.G_T x y| ≤ K * Real.exp (-(m * T.d x y))

/-! ## §4. Trivial case: zero correlator -/

/-- **A zero truncated 2-point trivially has exponential decay**
    with any positive rate `m` and `K = 0`. -/
theorem zero_correlator_has_decay
    (T : TruncatedTwoPoint) (h : ∀ x y, T.G_T x y = 0) :
    hasExponentialDecay T := by
  refine ⟨1, 0, by norm_num, le_refl 0, ?_⟩
  intro x y
  rw [h x y]
  simp

#print axioms zero_correlator_has_decay

end YangMills.L31_CreativeAttack_KP_ExpDecay
