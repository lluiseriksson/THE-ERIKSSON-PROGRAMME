/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# SU(N) 't Hooft large-Nc limit (Phase 248)

't Hooft's large-Nc expansion: take `N → ∞` with `g²·N` fixed.

## Strategic placement

This is **Phase 248** of the L26_SU_N_PhysicsApplications block.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L26_SU_N_PhysicsApplications

/-! ## §1. The 't Hooft coupling -/

/-- **'t Hooft coupling**: `λ := g²·N`, fixed in the large-Nc limit. -/
def tHooftCoupling (g : ℝ) (N : ℕ) : ℝ := g ^ 2 * N

/-- **The 't Hooft coupling is non-negative when `g`, `N` real**. -/
theorem tHooftCoupling_nonneg (g : ℝ) (N : ℕ) :
    0 ≤ tHooftCoupling g N := by
  unfold tHooftCoupling
  exact mul_nonneg (sq_nonneg g) (by exact_mod_cast Nat.zero_le N)

#print axioms tHooftCoupling_nonneg

/-! ## §2. The large-N limit prescription -/

/-- **Large-N prescription**: take `g(N) = √(λ/N)` for fixed `λ`. -/
noncomputable def g_largeN (lambda : ℝ) (N : ℕ) : ℝ :=
  Real.sqrt (lambda / N)

/-- **At fixed λ, `g(N)·N²` ?** trivially from the formula. -/
theorem g_largeN_squared (lambda : ℝ) (N : ℕ) (hλ : 0 ≤ lambda) (hN : 1 ≤ N) :
    (g_largeN lambda N) ^ 2 = lambda / N := by
  unfold g_largeN
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN
  have h_div_nn : 0 ≤ lambda / N := div_nonneg hλ hN_pos.le
  exact Real.sq_sqrt h_div_nn

#print axioms g_largeN_squared

/-! ## §3. The 't Hooft coupling at large-N is `λ`. -/

/-- **'t Hooft coupling at the large-N prescription equals `λ`**. -/
theorem tHooftCoupling_at_largeN (lambda : ℝ) (N : ℕ) (hλ : 0 ≤ lambda) (hN : 1 ≤ N) :
    tHooftCoupling (g_largeN lambda N) N = lambda := by
  unfold tHooftCoupling
  rw [g_largeN_squared lambda N hλ hN]
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN
  field_simp

#print axioms tHooftCoupling_at_largeN

end YangMills.L26_SU_N_PhysicsApplications
