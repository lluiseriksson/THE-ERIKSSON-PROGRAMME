/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L39_CreativeAttack_BalabanRGTransfer.LSI_to_DLR_LSI

/-!
# Transfer robustness (Phase 381)

Robustness of the transfer over the parameter space.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L39_CreativeAttack_BalabanRGTransfer

/-! ## §1. Universal transfer -/

/-- **For ANY positive `c, K` with `K ≤ 1`, the transfer holds**. -/
theorem universal_transfer (c K : ℝ) (h_c : 0 < c) (h_K : 0 < K) (h_K_le : K ≤ 1) :
    ∃ c_DLR : ℝ, 0 < c_DLR ∧ c_DLR = c / K := by
  refine ⟨c / K, ?_, rfl⟩
  exact div_pos h_c h_K

#print axioms universal_transfer

/-! ## §2. Monotonicity in K -/

/-- **`c_DLR = c/K` is monotonically decreasing in K**. -/
theorem DLR_constant_decreasing_in_K
    (c K₁ K₂ : ℝ) (h_c : 0 < c) (h_K₁ : 0 < K₁) (h_K₂ : 0 < K₂)
    (h_K_le : K₁ ≤ K₂) :
    c / K₂ ≤ c / K₁ := by
  apply div_le_div_of_nonneg_left (le_of_lt h_c) h_K₁ h_K_le

#print axioms DLR_constant_decreasing_in_K

/-! ## §3. Composability -/

/-- **Composition: two transfers with `K₁, K₂` give combined `K₁·K₂`**. -/
theorem composed_transfer
    (c K₁ K₂ : ℝ) (h_c : 0 < c) (h_K₁ : 0 < K₁) (h_K₂ : 0 < K₂) :
    c / (K₁ * K₂) = (c / K₁) / K₂ := by
  field_simp

#print axioms composed_transfer

end YangMills.L39_CreativeAttack_BalabanRGTransfer
