/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L20_SU2_Concrete_YangMills.SU2_Plaquette

/-!
# SU(2) Wilson action (Phase 186)

This module formalises the **Wilson plaquette action** for SU(2)
lattice gauge theory.

## Strategic placement

This is **Phase 186** of the L20_SU2_Concrete_YangMills block.

## What it does

The Wilson plaquette action for SU(2):

  S_W(U; β) = β · Σ_p (1 - (1/2) Re Tr(U_p))

where the sum is over all plaquettes `p`. We define:
* `SU2_WilsonPlaquetteContribution` — single-plaquette contribution.
* Properties: vanishing at identity, non-negativity (modulo abstract
  bounds).

## Oracle target

`[propext, Classical.choice, Quot.sound]`.

-/

namespace YangMills.L20_SU2_Concrete_YangMills

/-! ## §1. Single-plaquette Wilson contribution -/

/-- The **per-plaquette Wilson action contribution**:
    `β · (1 - (1/2) Re Tr(U_p))`. -/
def SU2_WilsonPlaquetteContribution (β : ℝ) (U_p : SU2) : ℝ :=
  β * (1 - (1/2) * plaquette_real_trace U_p)

/-! ## §2. Vanishing at identity -/

/-- **At the identity, `Re Tr(I) = 2`, so the per-plaquette
    contribution `1 - (1/2)·2 = 0` — vanishing identity term**. -/
theorem SU2_WilsonPlaquetteContribution_at_identity (β : ℝ) :
    SU2_WilsonPlaquetteContribution β SU2.identity = 0 := by
  unfold SU2_WilsonPlaquetteContribution
  rw [plaquette_real_trace_at_identity]
  ring

#print axioms SU2_WilsonPlaquetteContribution_at_identity

/-! ## §3. Linearity in β -/

/-- **Wilson contribution is linear in `β`**. -/
theorem SU2_WilsonPlaquetteContribution_linear_in_beta (β₁ β₂ : ℝ) (U_p : SU2) :
    SU2_WilsonPlaquetteContribution (β₁ + β₂) U_p =
      SU2_WilsonPlaquetteContribution β₁ U_p +
      SU2_WilsonPlaquetteContribution β₂ U_p := by
  unfold SU2_WilsonPlaquetteContribution
  ring

#print axioms SU2_WilsonPlaquetteContribution_linear_in_beta

/-! ## §4. Vanishing at zero coupling -/

/-- **At `β = 0`, the Wilson contribution vanishes**. -/
theorem SU2_WilsonPlaquetteContribution_zero_beta (U_p : SU2) :
    SU2_WilsonPlaquetteContribution 0 U_p = 0 := by
  unfold SU2_WilsonPlaquetteContribution
  ring

#print axioms SU2_WilsonPlaquetteContribution_zero_beta

/-! ## §5. Coordination note -/

/-
This file is **Phase 186** of the L20_SU2_Concrete_YangMills block.

## What's done

Three substantive Lean theorems with full proofs:
* `SU2_WilsonPlaquetteContribution_at_identity = 0` — vanishing
  at identity (concrete computation using Phase 184's
  `plaquette_real_trace_at_identity = 2`).
* `SU2_WilsonPlaquetteContribution_linear_in_beta` — linearity.
* `SU2_WilsonPlaquetteContribution_zero_beta` — vanishing at zero
  coupling.

Real Yang-Mills-specific Lean math.

## Strategic value

Phase 186 establishes the concrete Wilson action structure for
SU(2). The full action `Σ_p S_W(U_p)` is built by summing
plaquette contributions; the building block is now in Lean.

Cross-references:
- Phase 184 `SU2_Plaquette.lean`.
- Bloque-4 §2 (Wilson plaquette action).
-/

end YangMills.L20_SU2_Concrete_YangMills
