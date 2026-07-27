/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson

O-3b endpoint: a single named statement combining a gauge system, a temporal
splitting, the genuine Z_2 Wilson weight at positive coupling, and reflection
positivity.

Charter: docs/O-BRIDGE-CHARTER.md, AMENDMENT 6.
-/

import Mathlib
import YangMills.OS.ReflectionSplitting
import YangMills.OS.WilsonCharCombo

/-!
# O-3b endpoint — one instance, all four ingredients

## Why this module exists

The reflection-positivity development had its non-vacuity split across two
witnesses: a concrete splitting whose weight was constant (so its physics
content was nil), and the genuine `Z_2` Wilson weight proved to be a
non-negative character combination separately.  Nothing named a single object
carrying **all** of

* a gauge system with a nontrivial reflection,
* a concrete splitting of its configuration space across the plane,
* the real Wilson Boltzmann factor at `β > 0`, and
* the conclusion of reflection positivity.

`z2Wilson_reflectionPositive` is that statement, and
`z2WilsonSystem_nondegenerate` records that the weight it uses is genuinely
non-constant, so the endpoint is not the degenerate `β = 0` one.

## The system

Two edges exchanged by the time reflection, and one plaquette whose boundary is
both of them.  Its holonomy is therefore `x + y`, which in `Z_2` equals
`x - y`: the plaquette genuinely **straddles the reflection plane**, and the
whole Gibbs weight is the crossing kernel, with no half-space factor at all.
That is the smallest system in which reflection positivity says anything, and
unlike the earlier witness its weight is the real thing.

It is small.  A full temporal box with spatial extent, several time slices and
plaquettes of all three kinds (wholly positive, wholly negative, crossing) is
not treated here; the splitting interface is what such a box would have to
discharge, and doing so is geometric bookkeeping that this module does not
perform.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.OS

set_option linter.unusedSectionVars false

/-- In `Z_2` addition and subtraction agree, so a plaquette with both edges in
its boundary has holonomy `x - y`: it straddles the plane. -/
theorem zmod_two_add_eq_sub (a b : ZMod 2) : a + b = a - b := by
  revert a b
  decide

/-- The gauge system: two edges exchanged by the reflection, one plaquette
containing both, and the genuine `Z_2` Wilson factor. -/
noncomputable def z2WilsonSystem (β : ℝ) : GaugeData 2 (Fin 2) (Fin 1) where
  inc := fun _ _ => 1
  weight := z2Wilson β
  weight_pos := z2Wilson_pos β
  refl := fun e => if e = 0 then 1 else 0
  refl_refl := by decide

/-- The splitting: the two edges are the two halves, the reflection is the
swap, there is no half-space factor, and the crossing kernel is the Wilson
weight of the straddling plaquette. -/
noncomputable def z2WilsonSplitting (β : ℝ) :
    ReflectionSplitting (z2WilsonSystem β) (ZMod 2) where
  split :=
    { toFun := fun U => (U 0, U 1)
      invFun := fun p => fun e => if e = 0 then p.1 else p.2
      left_inv := by
        intro U
        funext e
        fin_cases e <;> simp
      right_inv := by
        intro p
        simp }
  split_refl := by
    intro U
    simp [reflConfig, z2WilsonSystem]
  w := fun _ => 1
  w_pos := fun _ => one_pos
  K := fun x y => ((z2Wilson β (x - y) : ℝ) : ℂ)
  factor := by
    intro U
    -- the anonymous `Equiv`'s projections are definitionally `U 0` and `U 1`,
    -- so `show` puts the goal in reduced form without a rewrite
    show ((boltz (z2WilsonSystem β) U : ℝ) : ℂ)
        = ((1 : ℝ) : ℂ) * ((1 : ℝ) : ℂ) * ((z2Wilson β (U 0 - U 1) : ℝ) : ℂ)
    have hb : boltz (z2WilsonSystem β) U = z2Wilson β (U 0 + U 1) := by
      simp [boltz, z2WilsonSystem, hol, Fin.sum_univ_two]
    rw [hb, zmod_two_add_eq_sub]
    push_cast
    ring

/-- **THE ENDPOINT.**  For the `Z_2` gauge system with the genuine Wilson
Boltzmann factor at non-negative coupling, with its temporal reflection and the
concrete splitting of its configuration space, the Osterwalder--Seiler pairing
of any observable of one half against its reflection is a non-negative real.

This is reflection positivity obtained by *discharging* a gauge system, a
splitting and a character expansion — not by assuming a pairing, and not with a
constant weight. -/
theorem z2Wilson_reflectionPositive {β : ℝ} (hβ : 0 ≤ β) (F : ZMod 2 → ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧ osPairing (z2WilsonSplitting β) F = (r : ℂ) :=
  osPairing_nonneg _ (z2Wilson_isCharCombo hβ) F

/-- The endpoint is not the degenerate `β = 0` instance: at positive coupling
the Wilson weight takes two different values, so the Gibbs measure is genuinely
non-uniform. -/
theorem z2WilsonSystem_nondegenerate {β : ℝ} (hβ : 0 < β) :
    (z2WilsonSystem β).weight 0 ≠ (z2WilsonSystem β).weight 1 := by
  simp only [z2WilsonSystem, z2Wilson]
  norm_num
  intro hcon
  have : Real.exp (-β) < Real.exp β := Real.exp_lt_exp.mpr (by linarith)
  linarith [hcon]

/-- And the reflection of the endpoint system genuinely exchanges the two
edges, so the splitting is not the identity. -/
theorem z2WilsonSystem_refl_ne_id (β : ℝ) : (z2WilsonSystem β).refl ≠ id := by
  intro h
  have := congrFun h 0
  simp [z2WilsonSystem] at this

end YangMills.OS
