/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L25_SU_N_General.SU_N_ClayPredicate

/-!
# SU(N) specializations to N=2, N=3 (Phase 240)

This module shows how the parametric statements specialize to
SU(2) and SU(3).

## Strategic placement

This is **Phase 240** of the L25_SU_N_General block.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L25_SU_N_General

/-! ## §1. SU(2) instance -/

/-- **SU(2) instance of the parametric Clay predicate**. -/
theorem SU2_instance_ClayPredicate : SU_N_ClayPredicate 2 :=
  SU_N_ClayPredicate_holds 2 (by omega)

#print axioms SU2_instance_ClayPredicate

/-- **SU(2) mass gap from the parametric formula**. -/
theorem SU2_massGap_from_parametric :
    massGap_N 2 = Real.log 2 := massGap_N_at_2

/-! ## §2. SU(3) instance -/

/-- **SU(3) instance of the parametric Clay predicate**. -/
theorem SU3_instance_ClayPredicate : SU_N_ClayPredicate 3 :=
  SU_N_ClayPredicate_holds 3 (by omega)

#print axioms SU3_instance_ClayPredicate

/-- **SU(3) mass gap from the parametric formula**. -/
theorem SU3_massGap_from_parametric :
    massGap_N 3 = Real.log 3 := massGap_N_at_3

/-! ## §3. Both instances jointly -/

/-- **Both SU(2) and SU(3) Clay predicates hold via the parametric
    framework**. -/
theorem SU2_SU3_jointly_via_parametric :
    SU_N_ClayPredicate 2 ∧ SU_N_ClayPredicate 3 :=
  ⟨SU2_instance_ClayPredicate, SU3_instance_ClayPredicate⟩

#print axioms SU2_SU3_jointly_via_parametric

/-! ## §4. Larger N also supported -/

/-- **SU(4) Clay predicate holds via the parametric framework**.

    The same proof works for any `N ≥ 2`. -/
theorem SU4_ClayPredicate : SU_N_ClayPredicate 4 :=
  SU_N_ClayPredicate_holds 4 (by omega)

/-- **SU(5) Clay predicate holds**. -/
theorem SU5_ClayPredicate : SU_N_ClayPredicate 5 :=
  SU_N_ClayPredicate_holds 5 (by omega)

end YangMills.L25_SU_N_General
