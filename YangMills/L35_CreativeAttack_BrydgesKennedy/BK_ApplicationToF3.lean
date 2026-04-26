/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L35_CreativeAttack_BrydgesKennedy.BK_PerEdgeBound

/-!
# BK application to F3-Mayer (Phase 339)

Application of the BK bound to control F3-Mayer expansion terms.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L35_CreativeAttack_BrydgesKennedy

/-! ## §1. F3-Mayer term bound from BK -/

/-- **F3-Mayer single-edge contribution bound**: for an edge with
    coupling β and `|β| · V ≤ T`, the contribution is bounded by
    `T · exp(T)`. -/
theorem F3Mayer_edge_bound (β V T : ℝ) (h_bound : |β * V| ≤ T) :
    |Real.exp (β * V) - 1| ≤ |β * V| * Real.exp (|β * V|) := by
  exact BK_per_edge_bound (β * V)

#print axioms F3Mayer_edge_bound

/-! ## §2. F3-Mayer at small β, V bounded -/

/-- **At small β with `|V| ≤ V_max`, the F3-Mayer edge contribution
    is small**: `|exp(βV) - 1| ≤ |β V| · exp(|β V|) ≤ |β| · V_max · exp(|β| · V_max)`. -/
theorem F3Mayer_small_beta_bound
    (β V V_max : ℝ) (h_V_bound : |V| ≤ V_max) (h_β_nn : 0 ≤ β) :
    |Real.exp (β * V) - 1| ≤ β * V_max * Real.exp (β * V_max) := by
  have h_βV_le : |β * V| ≤ β * V_max := by
    rw [abs_mul, abs_of_nonneg h_β_nn]
    exact mul_le_mul_of_nonneg_left h_V_bound h_β_nn
  have h_exp_le : Real.exp (|β * V|) ≤ Real.exp (β * V_max) :=
    Real.exp_le_exp.mpr h_βV_le
  have h_abs_nn : 0 ≤ |β * V| := abs_nonneg _
  have h_β_V_max_nn : 0 ≤ β * V_max := by
    have : 0 ≤ V_max := le_trans (abs_nonneg V) h_V_bound
    exact mul_nonneg h_β_nn this
  calc |Real.exp (β * V) - 1|
      ≤ |β * V| * Real.exp (|β * V|) := BK_per_edge_bound _
    _ ≤ (β * V_max) * Real.exp (β * V_max) := by
        apply mul_le_mul h_βV_le h_exp_le (Real.exp_pos _).le h_β_V_max_nn

#print axioms F3Mayer_small_beta_bound

end YangMills.L35_CreativeAttack_BrydgesKennedy
