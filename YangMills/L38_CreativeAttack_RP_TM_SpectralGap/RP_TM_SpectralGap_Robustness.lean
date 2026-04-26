/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L38_CreativeAttack_RP_TM_SpectralGap.T_SpectralGap_Existence

/-!
# RP+TM spectral gap robustness (Phase 371)

Robustness across all `(opNorm, δ)` pairs.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L38_CreativeAttack_RP_TM_SpectralGap

/-! ## §1. Universal robustness -/

/-- **Universal robustness**: for any spectral-gap data, the mass
    gap is positive. -/
theorem universal_mass_gap_positive (sgd : SpectralGapData) :
    0 < massGapFromSpectralData sgd := massGapFromSpectralData_pos sgd

/-! ## §2. Monotonicity -/

/-- **Mass gap is monotonically increasing in the gap fraction**:
    larger `δ/opNorm` ⇒ larger mass gap. -/
theorem mass_gap_monotone_in_gap_fraction
    (opNorm δ₁ δ₂ : ℝ) (h_opNorm_pos : 0 < opNorm)
    (h_δ₁_pos : 0 < δ₁) (h_δ₁_lt : δ₁ < opNorm)
    (h_δ₂_pos : 0 < δ₂) (h_δ₂_lt : δ₂ < opNorm)
    (h_δ_le : δ₁ ≤ δ₂) :
    Real.log (opNorm / (opNorm - δ₁)) ≤
      Real.log (opNorm / (opNorm - δ₂)) := by
  have h₁_pos : 0 < opNorm - δ₁ := by linarith
  have h₂_pos : 0 < opNorm - δ₂ := by linarith
  have h_div₁_pos : 0 < opNorm / (opNorm - δ₁) := div_pos h_opNorm_pos h₁_pos
  apply Real.log_le_log h_div₁_pos
  rw [div_le_div_iff h₁_pos h₂_pos]
  nlinarith

#print axioms mass_gap_monotone_in_gap_fraction

end YangMills.L38_CreativeAttack_RP_TM_SpectralGap
