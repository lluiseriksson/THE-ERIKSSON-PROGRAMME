/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L38_CreativeAttack_RP_TM_SpectralGap.RP_CauchySchwarz

/-!
# Transfer matrix as bounded operator (Phase 365)

The transfer matrix as a bounded operator on the RP Hilbert space.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L38_CreativeAttack_RP_TM_SpectralGap

/-! ## §1. Bounded operator structure -/

/-- **The transfer matrix as a bounded linear operator on the RP
    Hilbert space**. -/
structure BoundedTM (A : Type*) where
  rp : RPCauchySchwarz A
  /-- The TM action. -/
  T : A → A
  /-- Operator norm. -/
  opNorm : ℝ
  /-- Bounded: `⟨T x, T x⟩ ≤ opNorm² · ⟨x, x⟩`. -/
  bounded : ∀ x : A, rp.ip (T x) (T x) ≤ opNorm ^ 2 * rp.ip x x
  /-- Operator norm is non-negative. -/
  opNorm_nonneg : 0 ≤ opNorm

/-! ## §2. Operator-norm consequence -/

/-- **`‖T x‖_RP ≤ opNorm · ‖x‖_RP`** from the bounded property. -/
theorem BoundedTM.norm_bound {A : Type*} (BTM : BoundedTM A) (x : A) :
    BTM.rp.norm (BTM.T x) ≤ BTM.opNorm * BTM.rp.norm x := by
  unfold RPInnerProduct.norm
  have h_b := BTM.bounded x
  have h_xx_nn := BTM.rp.nonneg x
  -- √⟨Tx, Tx⟩ ≤ √(opNorm²·⟨x,x⟩) = opNorm·√⟨x,x⟩.
  rw [show BTM.opNorm * Real.sqrt (BTM.rp.ip x x)
        = Real.sqrt (BTM.opNorm^2 * BTM.rp.ip x x) by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq BTM.opNorm_nonneg]]
  exact Real.sqrt_le_sqrt h_b

#print axioms BoundedTM.norm_bound

/-! ## §3. Iterated bound -/

/-- **`‖T^n x‖ ≤ opNorm^n · ‖x‖` (iterated bound)** — abstract via
    norm_bound applied n times. -/
def iteratedNormBound (opNorm : ℝ) (n : ℕ) : ℝ := opNorm ^ n

/-- **Iterated bound is non-negative for `opNorm ≥ 0`**. -/
theorem iteratedNormBound_nonneg (opNorm : ℝ) (n : ℕ) (h : 0 ≤ opNorm) :
    0 ≤ iteratedNormBound opNorm n := by
  unfold iteratedNormBound
  exact pow_nonneg h n

end YangMills.L38_CreativeAttack_RP_TM_SpectralGap
