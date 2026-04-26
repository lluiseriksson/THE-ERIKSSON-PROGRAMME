/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Homogeneity index (Phase 384)

The set of homogeneities A in the regularity structure.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L40_CreativeAttack_HairerRegularity

/-! ## §1. Homogeneities -/

/-- **Homogeneity values** for Yang-Mills:
    `α_i = i/2` for i = 0, 1, 2, 3 (placeholder values).

    This corresponds to the typical scaling for stochastic
    quantization of YM in 4D. -/
def homogeneity (i : ℕ) : ℝ := (i : ℝ) / 2

theorem homogeneity_at_0 : homogeneity 0 = 0 := by
  unfold homogeneity; simp

theorem homogeneity_at_1 : homogeneity 1 = 1/2 := by
  unfold homogeneity; norm_num

theorem homogeneity_at_2 : homogeneity 2 = 1 := by
  unfold homogeneity; norm_num

theorem homogeneity_at_3 : homogeneity 3 = 3/2 := by
  unfold homogeneity; norm_num

#print axioms homogeneity_at_3

/-! ## §2. Increasing -/

/-- **Homogeneities are strictly increasing**. -/
theorem homogeneity_strictMono : StrictMono homogeneity := by
  intro a b hab
  unfold homogeneity
  have : (a : ℝ) < b := by exact_mod_cast hab
  linarith

#print axioms homogeneity_strictMono

end YangMills.L40_CreativeAttack_HairerRegularity
