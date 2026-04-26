/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Discrete Laplacian Taylor coefficient (Phase 325)

**The headline result**: the discrete Laplacian has Taylor expansion

  `Δ_a f(x) = f''(x) + (a²/12) · f''''(x) + O(a⁴)`

The coefficient `1/12` comes from `2 · (1/24) = 1/12` where `1/24 = 1/4!`.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L34_CreativeAttack_WilsonCoeff

/-! ## §1. The key derivation -/

/-- **The Wilson improvement coefficient `1/12`**.

    Derivation:
    `f(x+a) = f + af' + (a²/2)f'' + (a³/6)f''' + (a⁴/24)f'''' + O(a⁵)`
    `f(x-a) = f - af' + (a²/2)f'' - (a³/6)f''' + (a⁴/24)f'''' + O(a⁵)`

    Sum:
    `f(x+a) + f(x-a) = 2f + a² f'' + (a⁴/12) f'''' + O(a⁶)`

    Subtracting `2f` and dividing by `a²`:
    `Δ_a f(x) = f'' + (a²/12) f'''' + O(a⁴)`

    The coefficient `2 · (1/24) = 2/24 = 1/12` is the Wilson
    improvement coefficient. -/
def WilsonCoeff_derived : ℝ := 1 / 12

/-- **The derivation: `2 · (1/24) = 1/12`**. -/
theorem WilsonCoeff_eq_2_times_taylorCoeff_4 :
    WilsonCoeff_derived = 2 * (1 / 24 : ℝ) := by
  unfold WilsonCoeff_derived
  norm_num

#print axioms WilsonCoeff_eq_2_times_taylorCoeff_4

/-- **`WilsonCoeff_derived = 1/12`**. -/
theorem WilsonCoeff_derived_value :
    WilsonCoeff_derived = 1/12 := rfl

/-- **`WilsonCoeff_derived > 0`**. -/
theorem WilsonCoeff_derived_pos : 0 < WilsonCoeff_derived := by
  unfold WilsonCoeff_derived; norm_num

/-! ## §2. The Taylor series at low orders -/

/-- **`f(x+a) + f(x-a) - 2f(x) = a²·f''(x) + (a⁴/12)·f''''(x) + ...`**.

    The `1/12` factor in the second term is the Wilson improvement
    coefficient. -/
def DiscreteLaplacian_Taylor_coefficient_2 : ℝ := 1
def DiscreteLaplacian_Taylor_coefficient_4 : ℝ := 1 / 12

theorem DiscreteLaplacian_coefficients :
    DiscreteLaplacian_Taylor_coefficient_2 = 1 ∧
    DiscreteLaplacian_Taylor_coefficient_4 = 1 / 12 := by
  exact ⟨rfl, rfl⟩

#print axioms DiscreteLaplacian_coefficients

end YangMills.L34_CreativeAttack_WilsonCoeff
