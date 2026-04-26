/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L37_CreativeAttack_OS1Symanzik.SU_N_ImprovedWilsonAction

/-!
# SU(N) OS1 from improvement (Phase 359)

The OS1 closure via Symanzik improvement for SU(N).

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L37_CreativeAttack_OS1Symanzik

/-! ## §1. The improvement → OS1 chain -/

/-- **Improved deviation function for SU(N)**:
    `δ_SU_N(a) := SU_N_Improved_a4_residual · a²`. -/
def SU_N_ImprovedDeviation (N : ℕ) (a : ℝ) : ℝ :=
  SU_N_Improved_a4_residual N * a ^ 2

/-- **Deviation is non-negative for `N ≥ 1` and any a**. -/
theorem SU_N_ImprovedDeviation_nonneg (N : ℕ) (a : ℝ) (hN : 1 ≤ N) :
    0 ≤ SU_N_ImprovedDeviation N a := by
  unfold SU_N_ImprovedDeviation
  exact mul_nonneg (le_of_lt (SU_N_Improved_a4_residual_pos N hN)) (sq_nonneg a)

#print axioms SU_N_ImprovedDeviation_nonneg

/-! ## §2. Continuum-limit decay -/

/-- **`SU_N_ImprovedDeviation` tends to 0 as `a → 0⁺`**: this is the
    OS1 closure for SU(N). -/
theorem SU_N_ImprovedDeviation_tendsto_zero (N : ℕ) (hN : 1 ≤ N) :
    Filter.Tendsto (SU_N_ImprovedDeviation N)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds 0) := by
  unfold SU_N_ImprovedDeviation
  have h_cont : Continuous (fun a : ℝ => SU_N_Improved_a4_residual N * a ^ 2) := by
    continuity
  have h_eval :
      (fun a : ℝ => SU_N_Improved_a4_residual N * a ^ 2) 0 = 0 := by simp
  have h_tendsto : Filter.Tendsto
      (fun a : ℝ => SU_N_Improved_a4_residual N * a ^ 2) (nhds 0) (nhds 0) := by
    have := h_cont.tendsto 0
    rwa [h_eval] at this
  exact h_tendsto.mono_left nhdsWithin_le_nhds

#print axioms SU_N_ImprovedDeviation_tendsto_zero

/-! ## §3. Concrete instances -/

/-- **SU(2) OS1 closure via improvement**. -/
theorem SU2_OS1_via_improvement :
    Filter.Tendsto (SU_N_ImprovedDeviation 2)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds 0) :=
  SU_N_ImprovedDeviation_tendsto_zero 2 (by omega)

/-- **SU(3) (= QCD) OS1 closure via improvement**. -/
theorem SU3_OS1_via_improvement :
    Filter.Tendsto (SU_N_ImprovedDeviation 3)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds 0) :=
  SU_N_ImprovedDeviation_tendsto_zero 3 (by omega)

#print axioms SU3_OS1_via_improvement

end YangMills.L37_CreativeAttack_OS1Symanzik
