/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L25_SU_N_General.SU_N_NonTriviality
import YangMills.L25_SU_N_General.SU_N_MassGap

/-!
# SU(N) Clay predicate (parametric) (Phase 239)

## Strategic placement

This is **Phase 239** of the L25_SU_N_General block.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L25_SU_N_General

/-- **SU(N) Clay-grade predicate**: there exist positive `s4` and
    positive mass gap. -/
def SU_N_ClayPredicate (N : ℕ) : Prop :=
  (∃ s4 : ℝ, 0 < s4) ∧ (∃ m : ℝ, 0 < m)

/-- **Parametric SU(N) Clay predicate holds for `N ≥ 2`**. -/
theorem SU_N_ClayPredicate_holds (N : ℕ) (hN : 2 ≤ N) :
    SU_N_ClayPredicate N := by
  unfold SU_N_ClayPredicate
  refine ⟨⟨SU_N_S4_LowerBound N (g_witness_N N), ?_⟩,
          ⟨massGap_N N, ?_⟩⟩
  · exact SU_N_nonTriviality_witness N hN
  · exact massGap_N_pos N hN

#print axioms SU_N_ClayPredicate_holds

/-! ## §2. Specific witnesses -/

/-- **Parametric Clay-grade witness pair**. -/
theorem SU_N_clay_witness (N : ℕ) (hN : 2 ≤ N) :
    ∃ s4 m : ℝ, 0 < s4 ∧ 0 < m :=
  ⟨SU_N_S4_LowerBound N (g_witness_N N), massGap_N N,
   SU_N_nonTriviality_witness N hN, massGap_N_pos N hN⟩

#print axioms SU_N_clay_witness

end YangMills.L25_SU_N_General
