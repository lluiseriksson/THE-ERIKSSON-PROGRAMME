/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L23_SU3_QCD_Concrete.SU3_Plaquette

/-!
# SU(3) Wilson action (Phase 216)

For SU(3): `S_W(U; β) = β · Σ_p (1 - (1/3) Re Tr(U_p))`.
Note `1/3` factor (vs `1/2` for SU(2)).

## Strategic placement

This is **Phase 216** of the L23_SU3_QCD_Concrete block.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L23_SU3_QCD_Concrete

/-- **SU(3) per-plaquette Wilson contribution**:
    `β · (1 - (1/3) Re Tr(U_p))`. -/
def SU3_WilsonPlaquetteContribution (β : ℝ) (U_p : SU3) : ℝ :=
  β * (1 - (1/3) * plaquette_real_trace U_p)

/-- **Vanishing at identity** for SU(3): `1 - (1/3)·3 = 0`. -/
theorem SU3_WilsonPlaquetteContribution_at_identity (β : ℝ) :
    SU3_WilsonPlaquetteContribution β SU3.identity = 0 := by
  unfold SU3_WilsonPlaquetteContribution
  rw [plaquette_real_trace_at_identity]
  ring

#print axioms SU3_WilsonPlaquetteContribution_at_identity

/-- **Linearity in β**. -/
theorem SU3_WilsonPlaquetteContribution_linear_in_beta (β₁ β₂ : ℝ) (U_p : SU3) :
    SU3_WilsonPlaquetteContribution (β₁ + β₂) U_p =
      SU3_WilsonPlaquetteContribution β₁ U_p +
      SU3_WilsonPlaquetteContribution β₂ U_p := by
  unfold SU3_WilsonPlaquetteContribution
  ring

#print axioms SU3_WilsonPlaquetteContribution_linear_in_beta

/-- **Vanishing at zero coupling**. -/
theorem SU3_WilsonPlaquetteContribution_zero_beta (U_p : SU3) :
    SU3_WilsonPlaquetteContribution 0 U_p = 0 := by
  unfold SU3_WilsonPlaquetteContribution
  ring

#print axioms SU3_WilsonPlaquetteContribution_zero_beta

end YangMills.L23_SU3_QCD_Concrete
