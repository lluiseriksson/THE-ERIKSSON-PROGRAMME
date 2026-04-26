/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# SU(3) lattice gauge basics (Phase 213) — QCD GAUGE GROUP

This module formalises **SU(3) lattice gauge theory** — the
**physical QCD gauge group**, in contrast to the toy SU(2) case
covered in L20.

## Strategic placement

This is **Phase 213** of the L23_SU3_QCD_Concrete block — the
**seventeenth long-cycle block**, raising the project from
toy-physics SU(2) to **physical-QCD SU(3)**.

## What it does

SU(3) link variables are 3×3 unitary matrices with determinant 1.
The Wilson action `S_W = -β Σ_p (2/3) Re Tr(U_p)` (note the `2/3`
normalisation for SU(3)) defines the lattice QCD gauge dynamics.

We define:
* `SU3` — the SU(3) group via Mathlib's `Matrix.specialUnitaryGroup (Fin 3) ℂ`.
* Basic SU(3) properties.
* Plus a `LatticeLink` and `GaugeConfig` parametrised over SU(3).

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L23_SU3_QCD_Concrete

/-! ## §1. The SU(3) group -/

/-- **SU(3)**: 3×3 special-unitary complex matrices.

    This is the **physical gauge group of QCD**: 3 colours of quarks,
    8 gluons (the dimension of the adjoint representation). -/
abbrev SU3 := Matrix.specialUnitaryGroup (Fin 3) ℂ

/-- **The identity element of SU(3)**. -/
def SU3.identity : SU3 := 1

/-- **SU(3) is a group**. -/
example : Group SU3 := inferInstance

/-! ## §2. Determinant property -/

/-- **Every SU(3) element has determinant 1**. -/
theorem SU3.det_eq_one (g : SU3) : g.val.det = 1 := g.property.2

#print axioms SU3.det_eq_one

/-! ## §3. Unitarity -/

/-- **Every SU(3) element is unitary**: `g · g* = I`. -/
theorem SU3.unitary (g : SU3) :
    g.val * g.val.conjTranspose = (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  exact (Matrix.mem_unitaryGroup_iff'.mp g.property.1)

#print axioms SU3.unitary

/-! ## §4. Identity properties -/

/-- **The identity SU(3) element has determinant 1**. -/
theorem SU3.identity_det :
    SU3.identity.val.det = 1 := SU3.det_eq_one SU3.identity

#print axioms SU3.identity_det

/-! ## §5. Lattice abstraction (parallel to L20) -/

/-- **Lattice-link index type**. -/
abbrev LatticeLink (Site : Type*) : Type _ := Site × Site

/-- **SU(3) gauge configuration**: SU(3) element per link. -/
abbrev GaugeConfig (Site : Type*) : Type _ := LatticeLink Site → SU3

/-! ## §6. Coordination note -/

/-
This file is **Phase 213** of the L23_SU3_QCD_Concrete block.

## What's done

Three substantive Lean theorems for the **physical QCD gauge group**:
* `SU3.det_eq_one` — determinant property.
* `SU3.unitary` — unitarity.
* `SU3.identity_det` — consistency at identity.

This is **physical QCD-relevant Lean content**: SU(3) is the actual
gauge group of strong interactions.

## Strategic value

Phase 213 is the project's **first physical-QCD content**. The
remaining L23 files build the QCD-specific machinery in parallel
to the SU(2) structure of L20.

Cross-references:
- Phase 183 `L20_SU2_Concrete_YangMills/SU2_LatticeGauge.lean` (parallel
  for SU(2)).
- Mathlib's `Matrix.specialUnitaryGroup`.
- Bloque-4 Yang-Mills setup (general N_c).
-/

end YangMills.L23_SU3_QCD_Concrete
