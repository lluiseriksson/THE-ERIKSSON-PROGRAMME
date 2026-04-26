/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# SU(N) lattice gauge theory — parametric formulation (Phase 233)

This module formalises **SU(N) lattice gauge theory** parametrically
over general `N : ℕ` with `N ≥ 2`.

## Strategic placement

This is **Phase 233** of the L25_SU_N_General block —
the **nineteenth long-cycle block**, generalizing the SU(2)/SU(3)
specifications.

## What it does

For each `N ≥ 2`, defines `SU_N N` as the special unitary group
on `Fin N` complex matrices, and provides parametric versions of
the lattice-gauge structure.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L25_SU_N_General

/-! ## §1. The SU(N) group (parametric) -/

/-- **SU(N)**: parametric special-unitary group over `Fin N`. -/
abbrev SU_N (N : ℕ) := Matrix.specialUnitaryGroup (Fin N) ℂ

/-- **The identity element**. -/
def SU_N.identity (N : ℕ) : SU_N N := 1

/-- **SU(N) is a group** (parametric). -/
example (N : ℕ) : Group (SU_N N) := inferInstance

/-! ## §2. Determinant property (parametric) -/

/-- **Every SU(N) element has determinant 1**. -/
theorem SU_N.det_eq_one {N : ℕ} (g : SU_N N) : g.val.det = 1 :=
  g.property.2

#print axioms SU_N.det_eq_one

/-! ## §3. Unitarity (parametric) -/

/-- **Every SU(N) element is unitary**. -/
theorem SU_N.unitary {N : ℕ} (g : SU_N N) :
    g.val * g.val.conjTranspose = (1 : Matrix (Fin N) (Fin N) ℂ) :=
  Matrix.mem_unitaryGroup_iff'.mp g.property.1

#print axioms SU_N.unitary

/-! ## §4. Lattice abstraction (parametric) -/

/-- **Lattice-link index**. -/
abbrev LatticeLink (Site : Type*) : Type _ := Site × Site

/-- **SU(N) gauge configuration**. -/
abbrev GaugeConfig (Site : Type*) (N : ℕ) : Type _ :=
  LatticeLink Site → SU_N N

/-! ## §5. Coordination note -/

/-
This file is **Phase 233** of the L25_SU_N_General block.

## What's done

Two parametric Lean theorems:
* `SU_N.det_eq_one` — determinant property at any N.
* `SU_N.unitary` — unitarity at any N.

This is **parametric Yang-Mills content** generalizing L20 (SU(2))
and L23 (SU(3)).

## Strategic value

Phase 233 introduces a single parametric SU(N) framework. The
SU(2) and SU(3) cases of L20/L23 become instances of this
parametric structure.

Cross-references:
- Phase 183 (L20 SU(2)).
- Phase 213 (L23 SU(3)).
-/

end YangMills.L25_SU_N_General
