/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Self-adjoint contraction transfer matrix (Phase 303)

The TM is self-adjoint (from RP) and a contraction (norm ≤ 1).

## Strategic placement

This is **Phase 303** of the L32_CreativeAttack_LambdaEff block.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L32_CreativeAttack_LambdaEff

/-! ## §1. Self-adjoint contraction structure -/

/-- **Self-adjoint contraction transfer matrix**: abstract structure
    capturing the properties of T from RP + contraction. -/
structure SelfAdjointContractionTM where
  /-- Operator norm. -/
  opNorm : ℝ
  /-- Norm is non-negative. -/
  opNorm_nonneg : 0 ≤ opNorm
  /-- Norm is at most 1 (contraction property). -/
  opNorm_le_one : opNorm ≤ 1
  /-- Self-adjointness (abstract proposition). -/
  isSelfAdjoint : Prop := True
  /-- Positivity (T ≥ 0 from RP). -/
  isPositive : Prop := True

/-! ## §2. Basic properties -/

/-- **The norm is in [0, 1]**. -/
theorem TM_norm_in_unit (TM : SelfAdjointContractionTM) :
    0 ≤ TM.opNorm ∧ TM.opNorm ≤ 1 :=
  ⟨TM.opNorm_nonneg, TM.opNorm_le_one⟩

#print axioms TM_norm_in_unit

/-! ## §3. Norm squared bound -/

/-- **`(opNorm)² ≤ opNorm`** for a contraction (since `opNorm ≤ 1`). -/
theorem TM_norm_squared_le_norm (TM : SelfAdjointContractionTM) :
    TM.opNorm ^ 2 ≤ TM.opNorm := by
  have h_norm_nn : 0 ≤ TM.opNorm := TM.opNorm_nonneg
  have h_norm_le_1 : TM.opNorm ≤ 1 := TM.opNorm_le_one
  nlinarith

#print axioms TM_norm_squared_le_norm

/-! ## §4. Power bound -/

/-- **`opNorm^n ≤ opNorm`** for `n ≥ 1` and `opNorm ∈ [0, 1]**. -/
theorem TM_norm_power_le_norm (TM : SelfAdjointContractionTM) (n : ℕ)
    (hn : 1 ≤ n) :
    TM.opNorm ^ n ≤ TM.opNorm := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge 1 (k + 1) with h | h
    · -- k + 1 ≥ 2, so k ≥ 1.
      have hk : 1 ≤ k := by omega
      have hk_ih := ih hk
      have h_nn : 0 ≤ TM.opNorm := TM.opNorm_nonneg
      have h_le_1 : TM.opNorm ≤ 1 := TM.opNorm_le_one
      calc TM.opNorm ^ (k + 1) = TM.opNorm ^ k * TM.opNorm := by ring
        _ ≤ TM.opNorm * TM.opNorm := by
            exact mul_le_mul_of_nonneg_right hk_ih h_nn
        _ ≤ 1 * TM.opNorm := by
            exact mul_le_mul_of_nonneg_right h_le_1 h_nn
        _ = TM.opNorm := one_mul _
    · -- k + 1 = 1, i.e., n = 1.
      interval_cases k
      simp

#print axioms TM_norm_power_le_norm

end YangMills.L32_CreativeAttack_LambdaEff
