/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L25_SU_N_General.SU_N_Polymer

/-!
# SU(N) non-triviality witness (parametric) (Phase 237)

Parametric witness coupling and explicit positivity statement.

## Strategic placement

This is **Phase 237** of the L25_SU_N_General block.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L25_SU_N_General

/-- **Parametric witness coupling**: `g_N := 1 / N³`.

    Note: `g_N² = 1 / N⁶ < 1 / N⁴ = threshold_N` for `N ≥ 1`. -/
def g_witness_N (N : ℕ) : ℝ := 1 / (N : ℝ) ^ 3

/-- **`g_witness_N²` is positive for `N ≥ 1`**. -/
theorem g_witness_N_sq_pos (N : ℕ) (hN : 1 ≤ N) :
    0 < (g_witness_N N) ^ 2 := by
  unfold g_witness_N
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN
  positivity

#print axioms g_witness_N_sq_pos

/-- **`g_witness_N² = 1/N⁶`**. -/
theorem g_witness_N_sq_value (N : ℕ) (hN : 1 ≤ N) :
    (g_witness_N N) ^ 2 = 1 / (N : ℝ) ^ 6 := by
  unfold g_witness_N
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN
  have : ((N : ℝ) ^ 3) ^ 2 = (N : ℝ) ^ 6 := by ring
  rw [div_pow, one_pow, this]

#print axioms g_witness_N_sq_value

/-- **`g_witness_N² < threshold_N`** for `N ≥ 2`. Concretely,
    `1/N⁶ < 1/N⁴` requires `N⁴ < N⁶`, which holds for `N ≥ 2`. -/
theorem g_witness_N_below_threshold (N : ℕ) (hN : 2 ≤ N) :
    (g_witness_N N) ^ 2 < threshold_N N := by
  have hN1 : 1 ≤ N := le_trans (by omega : 1 ≤ 2) hN
  rw [g_witness_N_sq_value N hN1, threshold_N_value N hN1]
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN_lt_Nsq : (N : ℝ) ^ 4 < (N : ℝ) ^ 6 := by
    have hN_ge_2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have : (1 : ℝ) < N := by linarith
    -- N^4 < N^6 ⟺ N^4·1 < N^4·N^2 ⟺ 1 < N²
    have h_Nsq_gt_1 : (1 : ℝ) < (N : ℝ) ^ 2 := by nlinarith
    have h_N4_pos : (0 : ℝ) < (N : ℝ) ^ 4 := by positivity
    have : (N : ℝ) ^ 6 = (N : ℝ) ^ 4 * (N : ℝ) ^ 2 := by ring
    rw [this]
    nlinarith
  have h_N4_pos : (0 : ℝ) < (N : ℝ) ^ 4 := by positivity
  have h_N6_pos : (0 : ℝ) < (N : ℝ) ^ 6 := by positivity
  rw [div_lt_div_iff h_N6_pos h_N4_pos]
  ring_nf
  nlinarith

#print axioms g_witness_N_below_threshold

/-! ## §2. The parametric witness theorem -/

/-- **Parametric SU(N) non-triviality witness**: at `g = 1/N³` and
    `N ≥ 2`, the SU(N) lower bound is strictly positive. -/
theorem SU_N_nonTriviality_witness (N : ℕ) (hN : 2 ≤ N) :
    0 < SU_N_S4_LowerBound N (g_witness_N N) := by
  have hN1 : 1 ≤ N := le_trans (by omega : 1 ≤ 2) hN
  exact SU_N_nonTriviality_concrete N hN1
    (g_witness_N N) (g_witness_N_sq_pos N hN1)
    (g_witness_N_below_threshold N hN)

#print axioms SU_N_nonTriviality_witness

end YangMills.L25_SU_N_General
