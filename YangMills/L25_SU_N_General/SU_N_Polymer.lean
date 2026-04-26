/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L25_SU_N_General.SU_N_TreeLevel

/-!
# SU(N) polymer remainder C_N (Phase 236)

## Strategic placement

This is **Phase 236** of the L25_SU_N_General block.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L25_SU_N_General

/-- **Parametric SU(N) polymer remainder prefactor**: `C_N := N²`
    (placeholder). -/
def C_N (N : ℕ) : ℝ := (N : ℝ) ^ 2

/-- **`C_N > 0` for `N ≥ 1`**. -/
theorem C_N_pos (N : ℕ) (hN : 1 ≤ N) : 0 < C_N N := by
  unfold C_N
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN
  positivity

#print axioms C_N_pos

/-! ## §2. Threshold -/

/-- **Parametric strict-positivity threshold**: `γ_N / C_N = 1/N⁴`. -/
def threshold_N (N : ℕ) : ℝ := gamma_N N / C_N N

/-- **The threshold equals `1 / N⁴`** for `N ≥ 1`. -/
theorem threshold_N_value (N : ℕ) (hN : 1 ≤ N) :
    threshold_N N = 1 / (N : ℝ) ^ 4 := by
  unfold threshold_N gamma_N C_N
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN_sq_pos : (0 : ℝ) < (N : ℝ)^2 := by positivity
  field_simp
  ring

#print axioms threshold_N_value

/-- **Threshold is positive for `N ≥ 1`**. -/
theorem threshold_N_pos (N : ℕ) (hN : 1 ≤ N) : 0 < threshold_N N := by
  rw [threshold_N_value N hN]
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN
  positivity

/-! ## §3. SU(N) lower bound -/

/-- **Parametric SU(N) 4-point lower bound**: `g²·γ_N - g⁴·C_N`. -/
def SU_N_S4_LowerBound (N : ℕ) (g : ℝ) : ℝ :=
  g ^ 2 * gamma_N N - g ^ 4 * C_N N

/-- **Lower bound vanishes at `g = 0`**. -/
theorem SU_N_S4_LowerBound_at_zero (N : ℕ) :
    SU_N_S4_LowerBound N 0 = 0 := by
  unfold SU_N_S4_LowerBound; simp

/-- **Concrete non-triviality at SU(N)**: at `0 < g² < 1/N⁴`,
    `SU_N_S4_LowerBound N g > 0`. -/
theorem SU_N_nonTriviality_concrete (N : ℕ) (hN : 1 ≤ N)
    (g : ℝ) (h_g_sq_pos : 0 < g ^ 2)
    (h_below : g ^ 2 < threshold_N N) :
    0 < SU_N_S4_LowerBound N g := by
  unfold SU_N_S4_LowerBound
  have h_C_pos := C_N_pos N hN
  have h_gamma_pos := gamma_N_pos N hN
  have h_gsq_C : g ^ 2 * C_N N < gamma_N N := by
    rw [threshold_N] at h_below
    rw [lt_div_iff h_C_pos] at h_below
    exact h_below
  have h_dom : g ^ 4 * C_N N < g ^ 2 * gamma_N N := by
    have : g ^ 4 = g ^ 2 * g ^ 2 := by ring
    rw [this]
    calc g ^ 2 * g ^ 2 * C_N N
        = g ^ 2 * (g ^ 2 * C_N N) := by ring
      _ < g ^ 2 * gamma_N N := (mul_lt_mul_left h_g_sq_pos).mpr h_gsq_C
  linarith

#print axioms SU_N_nonTriviality_concrete

end YangMills.L25_SU_N_General
