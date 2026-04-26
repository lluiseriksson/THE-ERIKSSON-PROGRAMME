/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# SU(N) parametric mass gap (Phase 238)

Parametric mass gap `m_N := log N` for `N ≥ 2`.

## Strategic placement

This is **Phase 238** of the L25_SU_N_General block.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L25_SU_N_General

/-- **Parametric SU(N) mass gap**: `m_N := log N` for `N ≥ 2`. -/
noncomputable def massGap_N (N : ℕ) : ℝ := Real.log N

/-- **`massGap_N N > 0` for `N ≥ 2`**. -/
theorem massGap_N_pos (N : ℕ) (hN : 2 ≤ N) : 0 < massGap_N N := by
  unfold massGap_N
  apply Real.log_pos
  have : (2 : ℝ) ≤ N := by exact_mod_cast hN
  linarith

#print axioms massGap_N_pos

/-- **Mass gap is monotone in N for `N ≥ 1`**. -/
theorem massGap_N_monotone (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) :
    massGap_N N ≤ massGap_N M := by
  unfold massGap_N
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN
  apply Real.log_le_log hN_pos
  exact_mod_cast hNM

#print axioms massGap_N_monotone

/-! ## §2. Concrete instances -/

/-- **`massGap_N 2 = log 2`** (SU(2)). -/
theorem massGap_N_at_2 : massGap_N 2 = Real.log 2 := by
  unfold massGap_N; norm_cast

/-- **`massGap_N 3 = log 3`** (SU(3)/QCD). -/
theorem massGap_N_at_3 : massGap_N 3 = Real.log 3 := by
  unfold massGap_N; norm_cast

#print axioms massGap_N_at_2
#print axioms massGap_N_at_3

/-! ## §3. Strict monotonicity -/

/-- **`m_2 < m_3`**: SU(3) gap exceeds SU(2) gap. -/
theorem massGap_N_2_lt_3 : massGap_N 2 < massGap_N 3 := by
  rw [massGap_N_at_2, massGap_N_at_3]
  exact Real.log_lt_log (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) < 3)

#print axioms massGap_N_2_lt_3

end YangMills.L25_SU_N_General
