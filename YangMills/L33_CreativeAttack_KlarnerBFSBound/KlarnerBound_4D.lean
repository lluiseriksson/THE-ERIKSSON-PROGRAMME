/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L33_CreativeAttack_KlarnerBFSBound.KlarnerBound_Proof

/-!
# Klarner bound in 4D (Phase 318)

Specialization to 4D Yang-Mills.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L33_CreativeAttack_KlarnerBFSBound

/-! ## §1. The 4D Klarner bound -/

/-- **In 4D, `2d - 1 = 7`**. -/
theorem twoD_minus_one_at_4D : (2 * 4 - 1 : ℕ) = 7 := by norm_num

/-- **In 4D, the Klarner bound is `a_n ≤ K · 7^n`**. -/
theorem KlarnerBound_4D (a : ℕ → ℕ)
    (h_pt : ∀ n, 1 ≤ n → a n ≤ 7 ^ n) :
    KlarnerBound 4 a := by
  apply KlarnerBound_from_pointwise 4 a (by norm_num)
  intro n hn
  rw [twoD_minus_one_at_4D]
  exact h_pt n hn

#print axioms KlarnerBound_4D

/-! ## §2. The placeholder satisfies 4D Klarner -/

/-- **`animalCount 4 n = 7^n`** (the placeholder formula). -/
theorem animalCount_4D_value (n : ℕ) :
    animalCount 4 n = 7 ^ n := by
  unfold animalCount
  congr 1

/-- **The 4D animal count satisfies the 4D Klarner bound**. -/
theorem animalCount_4D_satisfies_Klarner :
    KlarnerBound 4 (fun n => animalCount 4 n) :=
  animalCount_satisfies_Klarner 4 (by norm_num)

#print axioms animalCount_4D_satisfies_Klarner

/-! ## §3. Concrete numerical bounds in 4D -/

/-- **At n = 5 in 4D: `7^5 = 16807`**. -/
theorem animalCount_4D_at_5 : animalCount 4 5 = 16807 := by
  rw [animalCount_4D_value]; norm_num

/-- **At n = 10 in 4D: `7^10 = 282475249`**. -/
theorem animalCount_4D_at_10 : animalCount 4 10 = 282475249 := by
  rw [animalCount_4D_value]; norm_num

#print axioms animalCount_4D_at_10

end YangMills.L33_CreativeAttack_KlarnerBFSBound
