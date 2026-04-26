/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L35_CreativeAttack_BrydgesKennedy.BK_PerEdgeBound
import YangMills.L35_CreativeAttack_BrydgesKennedy.BK_TreeGraphFormula

/-!
# Bound on Mayer weight (Phase 336)

Combined bound on the full Mayer weight using the per-edge bound.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L35_CreativeAttack_BrydgesKennedy

/-! ## §1. The combined bound -/

/-- **For a graph with `k` edges, each with `|t_e| ≤ T`, the
    Mayer-weight contribution is at most `T^k · exp(k · T)`**.

    Stated as a function. -/
def MayerEdgesBound (k : ℕ) (T : ℝ) : ℝ :=
  T ^ k * Real.exp ((k : ℝ) * T)

/-- **Bound is non-negative for `T ≥ 0`**. -/
theorem MayerEdgesBound_nonneg (k : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    0 ≤ MayerEdgesBound k T := by
  unfold MayerEdgesBound
  exact mul_nonneg (pow_nonneg hT k) (Real.exp_pos _).le

#print axioms MayerEdgesBound_nonneg

/-! ## §2. The per-edge bound applied -/

/-- **At `k = 1`, the per-edge bound recovers `|exp(t) - 1| ≤ T·exp(T)`
    for `|t| ≤ T`**. -/
theorem MayerEdgesBound_one_edge (T t : ℝ) (h_t_le : |t| ≤ T) :
    |Real.exp t - 1| ≤ MayerEdgesBound 1 T := by
  unfold MayerEdgesBound
  -- Need: |exp(t) - 1| ≤ T^1 · exp(1 · T) = T · exp(T).
  -- We have |exp(t) - 1| ≤ |t| · exp(|t|) (per-edge bound)
  -- and |t| ≤ T, exp(|t|) ≤ exp(T).
  have h_per_edge := BK_per_edge_bound t
  have h_abs_t_le : |t| ≤ T := h_t_le
  have h_T_nn : 0 ≤ T := le_trans (abs_nonneg t) h_t_le
  have h_exp_le : Real.exp (|t|) ≤ Real.exp T := Real.exp_le_exp.mpr h_abs_t_le
  have h_abs_t_nn : 0 ≤ |t| := abs_nonneg t
  calc |Real.exp t - 1|
      ≤ |t| * Real.exp (|t|) := h_per_edge
    _ ≤ T * Real.exp T := by
        apply mul_le_mul h_abs_t_le h_exp_le (Real.exp_pos _).le h_T_nn
    _ = T ^ 1 * Real.exp (1 * T) := by ring

#print axioms MayerEdgesBound_one_edge

end YangMills.L35_CreativeAttack_BrydgesKennedy
