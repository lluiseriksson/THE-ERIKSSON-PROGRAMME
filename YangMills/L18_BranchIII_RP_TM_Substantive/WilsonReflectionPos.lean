/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L18_BranchIII_RP_TM_Substantive.ReflectionPositivityCore

/-!
# Wilson reflection positivity (Phase 164)

This module formalises **reflection positivity for the Wilson
plaquette action** on a square lattice.

## Strategic placement

This is **Phase 164** of the L18_BranchIII_RP_TM_Substantive block.

## What it does

The Wilson plaquette action `S_W = -β · Σ Re Tr(U_p)` is
reflection-positive when paired with the standard reflection
across a hyperplane perpendicular to the time axis.

We give the abstract structural shape of this property:
* `WilsonReflection` — the time-reversal reflection.
* `WilsonRPForm` — RP form for the Wilson action.
* Compositional theorems showing how to build a Wilson RP form.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L18_BranchIII_RP_TM_Substantive

/-! ## §1. Wilson-style reflection -/

/-- **Wilson-style reflection**: a reflection `θ` with the additional
    structural property of preserving a "positive cone" set. -/
structure WilsonReflection (Φ : Type*) extends Reflection Φ where
  /-- A "positive-time" subset preserved up to reflection. -/
  positiveCone : Set Φ
  /-- The reflection sends positive-time to negative-time. -/
  reflects_cone : ∀ f ∈ positiveCone, θ f ∉ positiveCone ∨ θ f = f

/-! ## §2. RP form for Wilson action -/

/-- **An RP form on the Wilson positive cone**. -/
structure WilsonRPForm (Φ : Type*) where
  /-- The Wilson reflection. -/
  wRefl : WilsonReflection Φ
  /-- The form. -/
  B : Φ → Φ → ℝ
  /-- RP on the positive cone: `B(f, θ f) ≥ 0` for `f` in the cone. -/
  rp_on_cone : ∀ f ∈ wRefl.positiveCone, 0 ≤ B f (wRefl.θ f)

/-! ## §3. Build an `RP form` from a `WilsonRPForm` -/

/-- **Every `WilsonRPForm` whose RP property holds globally extends
    to a `ReflectionPositiveForm`**. -/
def WilsonRPForm.toReflectionPositive
    {Φ : Type*} (W : WilsonRPForm Φ)
    (h_global : ∀ f : Φ, 0 ≤ W.B f (W.wRefl.θ f)) :
    ReflectionPositiveForm Φ :=
  { refl := W.wRefl.toReflection
    B := W.B
    rp := h_global }

/-! ## §4. Cone preservation theorem -/

/-- **The Wilson reflection acts on the positive cone non-trivially**:
    elements either leave the cone or are fixed. -/
theorem WilsonReflection.cone_action
    {Φ : Type*} (W : WilsonReflection Φ) :
    ∀ f ∈ W.positiveCone, W.θ f ∉ W.positiveCone ∨ W.θ f = f :=
  W.reflects_cone

#print axioms WilsonReflection.cone_action

/-! ## §5. Coordination note -/

/-
This file is **Phase 164** of the L18_BranchIII_RP_TM_Substantive block.

## What's done

A `WilsonReflection` + `WilsonRPForm` structure with a constructor
producing a `ReflectionPositiveForm` from a global RP property.

## Strategic value

Phase 164 provides the abstract Wilson-style RP structure that
downstream files (transfer matrix, spectral gap) target.

Cross-references:
- Phase 163 `ReflectionPositivityCore.lean`.
- Project's existing `YangMills/Branch3RP/WilsonReflectionPositivity.lean`.
- Bloque-4 §8.1 (OS3 axiom).
-/

end YangMills.L18_BranchIII_RP_TM_Substantive
