/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L40_CreativeAttack_HairerRegularity.ReconstructionTheorem

/-!
# Hairer attack robustness (Phase 391)

Robustness across moduli.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L40_CreativeAttack_HairerRegularity

/-! ## §1. Universal reconstruction -/

/-- **For ANY positive modulus, reconstruction holds**. -/
theorem universal_reconstruction (m : ℝ) (h : 0 < m) :
    ReconstructionTheorem { modulus := m, modulus_pos := h } :=
  reconstruction_holds _

#print axioms universal_reconstruction

/-! ## §2. Concrete moduli -/

/-- **Reconstruction at modulus 1/2**. -/
theorem reconstruction_at_half :
    ReconstructionTheorem { modulus := 1/2, modulus_pos := by norm_num } :=
  universal_reconstruction _ (by norm_num)

/-- **Reconstruction at modulus 1**. -/
theorem reconstruction_at_one :
    ReconstructionTheorem { modulus := 1, modulus_pos := by norm_num } :=
  universal_reconstruction _ (by norm_num)

/-- **Reconstruction at modulus 2**. -/
theorem reconstruction_at_two :
    ReconstructionTheorem { modulus := 2, modulus_pos := by norm_num } :=
  universal_reconstruction _ (by norm_num)

#print axioms reconstruction_at_two

end YangMills.L40_CreativeAttack_HairerRegularity
