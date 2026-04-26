/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Hot QCD and deconfinement (Phase 280)

QCD at high temperature undergoes a deconfinement transition.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L29_AdjacentTheories

/-- **Critical deconfinement temperature** `T_c ≈ 270 MeV` for pure
    SU(3) YM (placeholder = 1). -/
def Tc_QCD : ℝ := 1

theorem Tc_QCD_pos : 0 < Tc_QCD := by unfold Tc_QCD; norm_num

/-- **Below T_c, the theory is confined**. -/
def confined (T : ℝ) : Prop := T < Tc_QCD

/-- **Above T_c, the theory is deconfined**. -/
def deconfined (T : ℝ) : Prop := Tc_QCD < T

/-- **Confinement and deconfinement are mutually exclusive**. -/
theorem confined_deconfined_excl (T : ℝ) :
    ¬ (confined T ∧ deconfined T) := by
  intro ⟨hc, hd⟩
  unfold confined deconfined at hc hd
  linarith

#print axioms confined_deconfined_excl

/-- **Deconfinement at high T = 2 T_c**. -/
theorem high_T_deconfines : deconfined (2 * Tc_QCD) := by
  unfold deconfined
  have := Tc_QCD_pos
  linarith

#print axioms high_T_deconfines

end YangMills.L29_AdjacentTheories
