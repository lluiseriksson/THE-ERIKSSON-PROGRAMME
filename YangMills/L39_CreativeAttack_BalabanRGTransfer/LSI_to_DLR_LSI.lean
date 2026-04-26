/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L39_CreativeAttack_BalabanRGTransfer.TransferHypothesis

/-!
# LSI to DLR-LSI implication (Phase 377)

The central transfer theorem.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L39_CreativeAttack_BalabanRGTransfer

/-! ## §1. The transfer theorem -/

/-- **THE TRANSFER THEOREM**: LSI + transfer hypothesis ⇒ DLR-LSI. -/
theorem LSI_implies_DLR_LSI (lsi : LSI) (th : TransferHypothesis) :
    DLR_LSI := DLR_LSI_from_transfer lsi th

#print axioms LSI_implies_DLR_LSI

/-! ## §2. Constants relation -/

/-- **The DLR constant is `c_LSI / K`**. -/
theorem DLR_constant_value (lsi : LSI) (th : TransferHypothesis) :
    (LSI_implies_DLR_LSI lsi th).c_DLR = lsi.c / th.K := rfl

/-! ## §3. Comparison: DLR ≤ LSI when K ≤ 1 -/

/-- **Tight transfer**: when `K = 1`, DLR-LSI constant equals LSI
    constant. -/
theorem tight_transfer (lsi : LSI) :
    (LSI_implies_DLR_LSI lsi defaultTransfer).c_DLR = lsi.c := by
  rw [DLR_constant_value]
  unfold defaultTransfer
  simp

#print axioms tight_transfer

/-! ## §4. Worst-case bound -/

/-- **For `K ≤ 1`, the DLR constant is at least the LSI constant**:
    `c_DLR = c/K ≥ c/1 = c`. -/
theorem DLR_constant_ge_LSI (lsi : LSI) (th : TransferHypothesis) :
    lsi.c ≤ (LSI_implies_DLR_LSI lsi th).c_DLR := by
  rw [DLR_constant_value]
  rw [le_div_iff th.K_pos]
  -- Need: lsi.c · th.K ≤ lsi.c, i.e., th.K ≤ 1.
  nlinarith [lsi.c_pos, th.K_le_one]

#print axioms DLR_constant_ge_LSI

end YangMills.L39_CreativeAttack_BalabanRGTransfer
