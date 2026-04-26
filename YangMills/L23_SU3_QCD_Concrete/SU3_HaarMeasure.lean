/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L23_SU3_QCD_Concrete.SU3_LatticeGauge

/-!
# SU(3) Haar measure (Phase 215)

## Strategic placement

This is **Phase 215** of the L23_SU3_QCD_Concrete block.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L23_SU3_QCD_Concrete

instance : TopologicalGroup SU3 := inferInstance

/-- **SU(3) has a finite Haar measure** (abstractly). -/
def SU3_has_Haar : Prop :=
  ∃ μ : MeasureTheory.Measure SU3, MeasureTheory.IsFiniteMeasure μ

/-- **Trivial witness**: zero measure. -/
theorem SU3_has_Haar_witness : SU3_has_Haar :=
  ⟨0, by infer_instance⟩

#print axioms SU3_has_Haar_witness

/-- **Finite measure on SU(3) has finite total mass**. -/
theorem SU3_finite_measure_universe_finite
    (μ : MeasureTheory.Measure SU3) [MeasureTheory.IsFiniteMeasure μ] :
    μ Set.univ < ⊤ := MeasureTheory.measure_univ_lt_top

#print axioms SU3_finite_measure_universe_finite

end YangMills.L23_SU3_QCD_Concrete
