/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L38_CreativeAttack_RP_TM_SpectralGap.RP_InnerProduct

/-!
# Cauchy-Schwarz on RP inner product (Phase 364)

The Cauchy-Schwarz inequality for the RP-induced inner product.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L38_CreativeAttack_RP_TM_SpectralGap

/-! ## §1. Cauchy-Schwarz hypothesis -/

/-- **Hypothesis**: the RP inner product satisfies Cauchy-Schwarz.
    For an honest inner product, this follows from positive
    semi-definiteness; we encode it as a hypothesis for abstract
    purposes. -/
structure RPCauchySchwarz (A : Type*) extends RPInnerProduct A where
  /-- The Cauchy-Schwarz inequality. -/
  CS : ∀ x y : A, (ip x y) ^ 2 ≤ ip x x * ip y y

/-! ## §2. Cauchy-Schwarz consequences -/

/-- **From CS, `|⟨x, y⟩| ≤ ‖x‖·‖y‖`**. -/
theorem RPCauchySchwarz.abs_le_norm_norm {A : Type*}
    (rp : RPCauchySchwarz A) (x y : A) :
    |rp.ip x y| ≤ Real.sqrt (rp.ip x x) * Real.sqrt (rp.ip y y) := by
  have h_CS := rp.CS x y
  have h_xx_nn := rp.nonneg x
  have h_yy_nn := rp.nonneg y
  -- |⟨x,y⟩|² ≤ ⟨x,x⟩·⟨y,y⟩, take sqrt of both sides.
  rw [show |rp.ip x y| = Real.sqrt ((rp.ip x y)^2) from (Real.sqrt_sq_eq_abs _).symm]
  rw [show Real.sqrt (rp.ip x x) * Real.sqrt (rp.ip y y)
        = Real.sqrt (rp.ip x x * rp.ip y y) from (Real.sqrt_mul h_xx_nn _).symm]
  exact Real.sqrt_le_sqrt h_CS

#print axioms RPCauchySchwarz.abs_le_norm_norm

/-! ## §3. Equality at zero -/

/-- **At `x = y` with `⟨x, x⟩ = 0`, CS gives `⟨x, y⟩² ≤ 0`**. -/
theorem RPCauchySchwarz.zero_norm_implies_zero_ip {A : Type*}
    (rp : RPCauchySchwarz A) (x y : A) (h_xx : rp.ip x x = 0) :
    rp.ip x y = 0 := by
  have h_CS := rp.CS x y
  rw [h_xx] at h_CS
  rw [zero_mul] at h_CS
  have h_sq_nn : 0 ≤ (rp.ip x y) ^ 2 := sq_nonneg _
  have h_eq : (rp.ip x y) ^ 2 = 0 := le_antisymm h_CS h_sq_nn
  exact pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0) |>.mp h_eq

#print axioms RPCauchySchwarz.zero_norm_implies_zero_ip

end YangMills.L38_CreativeAttack_RP_TM_SpectralGap
