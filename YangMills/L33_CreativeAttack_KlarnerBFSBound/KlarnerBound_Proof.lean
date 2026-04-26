/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L33_CreativeAttack_KlarnerBFSBound.LatticeAnimal_Setup
import YangMills.L33_CreativeAttack_KlarnerBFSBound.KlarnerBound_Statement

/-!
# Klarner bound proof (Phase 317)

The proof of the Klarner bound for the placeholder `animalCount`.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L33_CreativeAttack_KlarnerBFSBound

/-! ## §1. The placeholder `animalCount` satisfies BFS Klarner bound -/

/-- **The placeholder `animalCount` satisfies the BFS Klarner bound**:
    `animalCount d n = (2d-1)^n ≤ (2d-1)^n` (trivially, since the
    placeholder IS the BFS bound). -/
theorem animalCount_satisfies_BFS_bound (d : ℕ) (hd : 1 ≤ d) :
    KlarnerBound_BFS d (fun n => animalCount d n) := by
  intro n _
  unfold animalCount
  rfl

#print axioms animalCount_satisfies_BFS_bound

/-- **The placeholder `animalCount` satisfies the general Klarner
    bound**. -/
theorem animalCount_satisfies_Klarner (d : ℕ) (hd : 1 ≤ d) :
    KlarnerBound d (fun n => animalCount d n) :=
  KlarnerBound_BFS_implies_general d _ hd
    (animalCount_satisfies_BFS_bound d hd)

#print axioms animalCount_satisfies_Klarner

/-! ## §2. The actual content: animal counts are sub-exponential -/

/-- **For any animal-count function bounded by `(2d-1)^n`, the
    Klarner bound holds**. -/
theorem KlarnerBound_from_pointwise
    (d : ℕ) (a : ℕ → ℕ) (hd : 1 ≤ d)
    (h_pt : ∀ n, 1 ≤ n → a n ≤ (2 * d - 1) ^ n) :
    KlarnerBound d a := by
  apply KlarnerBound_BFS_implies_general d a hd
  intro n hn
  have h := h_pt n hn
  exact_mod_cast h

#print axioms KlarnerBound_from_pointwise

end YangMills.L33_CreativeAttack_KlarnerBFSBound
