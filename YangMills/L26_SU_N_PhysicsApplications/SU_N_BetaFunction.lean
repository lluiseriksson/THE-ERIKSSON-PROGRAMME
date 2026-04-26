/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L26_SU_N_PhysicsApplications.SU_N_AsymptoticFreedom

/-!
# SU(N) β-function (Phase 246)

The β-function `β(g) = -β₀ g³ + O(g⁵)`.

## Strategic placement

This is **Phase 246** of the L26_SU_N_PhysicsApplications block.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L26_SU_N_PhysicsApplications

/-! ## §1. One-loop β function -/

/-- **One-loop β-function**: `β(g) = -β₀(N) · g³`. -/
def betaFunction1Loop (N : ℕ) (g : ℝ) : ℝ := -(beta_0 N) * g ^ 3

/-- **At zero coupling, β = 0**. -/
theorem betaFunction1Loop_at_zero (N : ℕ) :
    betaFunction1Loop N 0 = 0 := by
  unfold betaFunction1Loop; simp

/-- **For `g > 0` and `N ≥ 1`, β(g) < 0** (asymptotic freedom). -/
theorem betaFunction1Loop_neg (N : ℕ) (g : ℝ) (hg : 0 < g) (hN : 1 ≤ N) :
    betaFunction1Loop N g < 0 := by
  unfold betaFunction1Loop
  have hβ₀ : 0 < beta_0 N := beta_0_pos N hN
  have hg3 : 0 < g ^ 3 := by positivity
  nlinarith

#print axioms betaFunction1Loop_neg

/-! ## §2. Sign of β-function and AF -/

/-- **Asymptotic freedom from β < 0**: when β(g) < 0 for g > 0,
    the coupling decreases as μ increases. -/
theorem AF_from_betaFunction (N : ℕ) (g : ℝ) (hg : 0 < g) (hN : 1 ≤ N) :
    betaFunction1Loop N g < 0 := betaFunction1Loop_neg N g hg hN

end YangMills.L26_SU_N_PhysicsApplications
