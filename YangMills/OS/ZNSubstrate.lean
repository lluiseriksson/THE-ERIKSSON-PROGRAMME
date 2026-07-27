/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson

O-3a: substrate for the finite-gauge-group Osterwalder-Seiler chain.

Charter: docs/O-BRIDGE-CHARTER.md, AMENDMENT 6.
-/

import Mathlib

/-!
# O-3a — the finite gauge system, its Gibbs weight, and the time reflection

## What this brick is for

The O-1 arc proved a criterion about transfer operators and exhibited only
witnesses of the form `r·1 + (1-r)P` — operators built *from* the conclusion.
Both the adversarial audit and the external review named that as the arc's
remaining weakness: nothing showed the interface is consumable by an object
coming from a **measure**.  O-3 answers that by building the whole
Osterwalder–Seiler chain for a gauge theory whose gauge group is **finite**, so
that every expectation is a `Finset.sum` and no measure theory is needed.

This module is the substrate only: configurations, the Wilson weight, the
partition function, expectations, and the time reflection.  It proves nothing
about positivity of the reflection pairing — that is O-3b, the brick that can
kill the phase, and it is deliberately not anticipated here.

## The design decision worth recording

The lattice geometry is carried as **data** (`GaugeData`), not hard-coded: a
finite edge type, a finite plaquette type, a `ZMod N`-valued incidence
`inc : Plaq → Edge → ZMod N`, a strictly positive single-plaquette Boltzmann
factor, and an involution on edges.  For an abelian gauge group the plaquette
holonomy is the incidence-weighted sum of edge variables, so this covers `Z_N`
gauge theory on any lattice with any reflection, and the geometric bookkeeping
of a particular box does not have to be discharged before the analytic content
can be stated.

The price is that reflection invariance of the weight is a hypothesis
(`ReflInvariant`) rather than a consequence, since it is a property of the
geometry.  It is discharged concretely in the witness below.

## Non-vacuity, and an honest limit on it

`minimalSystem` inhabits the structure with `N ≥ 2`, two edges exchanged by the
reflection, and a genuinely reflection-invariant weight.  It is deliberately
minimal: its purpose is to show the structure is not empty and that
`ReflInvariant` is satisfiable, **not** to be a physically interesting lattice.
The `1+1`-dimensional box instance is registered for O-3b, where the plaquettes
that straddle the reflection plane are what the argument actually needs.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.OS

set_option linter.unusedSectionVars false

open Finset

/-! ## Configurations -/

/-- A gauge configuration assigns an element of `ZMod N` to every edge. -/
abbrev Config (N : ℕ) (Edge : Type*) := Edge → ZMod N

/-- The data of a finite abelian gauge system with a reflection: an incidence
matrix giving each plaquette's boundary, a strictly positive single-plaquette
Boltzmann factor, and an involution of the edge set (the time reflection). -/
structure GaugeData (N : ℕ) (Edge Plaq : Type*) where
  /-- Signed multiplicity of an edge in the boundary of a plaquette. -/
  inc : Plaq → Edge → ZMod N
  /-- The single-plaquette Boltzmann factor. -/
  weight : ZMod N → ℝ
  /-- It is strictly positive, so the Gibbs weight never vanishes. -/
  weight_pos : ∀ x, 0 < weight x
  /-- The time reflection, as a map on edges. -/
  refl : Edge → Edge
  /-- It is an involution. -/
  refl_refl : ∀ e, refl (refl e) = e

variable {N : ℕ} [NeZero N] {Edge Plaq : Type*}
variable [Fintype Edge] [DecidableEq Edge] [Fintype Plaq]

/-- The holonomy of a plaquette: the incidence-weighted sum of edge variables.
For an abelian gauge group this is the whole content of "the product around the
boundary". -/
def hol (G : GaugeData N Edge Plaq) (U : Config N Edge) (p : Plaq) : ZMod N :=
  ∑ e : Edge, G.inc p e * U e

/-- The Gibbs weight of a configuration: the product of the single-plaquette
factors over all plaquettes. -/
noncomputable def boltz (G : GaugeData N Edge Plaq) (U : Config N Edge) : ℝ :=
  ∏ p : Plaq, G.weight (hol G U p)

theorem boltz_pos (G : GaugeData N Edge Plaq) (U : Config N Edge) : 0 < boltz G U :=
  Finset.prod_pos fun _p _ => G.weight_pos _

/-- The partition function. -/
noncomputable def partition (G : GaugeData N Edge Plaq) : ℝ :=
  ∑ U : Config N Edge, boltz G U

theorem partition_pos (G : GaugeData N Edge Plaq) : 0 < partition G := by
  refine Finset.sum_pos (fun U _ => boltz_pos G U) ?_
  exact Finset.univ_nonempty

/-- The normalized expectation of a complex observable.  Every "integral" in
this development is this finite sum. -/
noncomputable def expect (G : GaugeData N Edge Plaq) (F : Config N Edge → ℂ) : ℂ :=
  (∑ U : Config N Edge, (boltz G U : ℂ) * F U) / (partition G : ℂ)

theorem partition_ne_zero (G : GaugeData N Edge Plaq) : ((partition G : ℂ)) ≠ 0 := by
  simpa using (ne_of_gt (partition_pos G))

@[simp] theorem expect_one (G : GaugeData N Edge Plaq) :
    expect G (fun _ => (1 : ℂ)) = 1 := by
  unfold expect
  simp only [mul_one]
  rw [show (∑ U : Config N Edge, (boltz G U : ℂ)) = ((partition G : ℝ) : ℂ) by
    unfold partition; push_cast; rfl]
  exact div_self (partition_ne_zero G)

theorem expect_add (G : GaugeData N Edge Plaq) (F₁ F₂ : Config N Edge → ℂ) :
    expect G (fun U => F₁ U + F₂ U) = expect G F₁ + expect G F₂ := by
  unfold expect
  rw [← add_div]
  congr 1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun U _ => by ring

theorem expect_smul (G : GaugeData N Edge Plaq) (c : ℂ) (F : Config N Edge → ℂ) :
    expect G (fun U => c * F U) = c * expect G F := by
  unfold expect
  rw [← mul_div_assoc]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun U _ => by ring

/-! ## The time reflection -/

/-- The reflection acting on configurations. -/
def reflConfig (G : GaugeData N Edge Plaq) (U : Config N Edge) : Config N Edge :=
  fun e => U (G.refl e)

theorem reflConfig_involutive (G : GaugeData N Edge Plaq) (U : Config N Edge) :
    reflConfig G (reflConfig G U) = U := by
  funext e
  simp only [reflConfig]
  rw [G.refl_refl]

/-- The reflection acting on observables, with the complex conjugation that the
Osterwalder--Seiler pairing carries. -/
noncomputable def reflObs (G : GaugeData N Edge Plaq) (F : Config N Edge → ℂ) :
    Config N Edge → ℂ :=
  fun U => starRingEnd ℂ (F (reflConfig G U))

theorem reflObs_involutive (G : GaugeData N Edge Plaq) (F : Config N Edge → ℂ) :
    reflObs G (reflObs G F) = F := by
  funext U
  simp only [reflObs, reflConfig_involutive]
  simp

/-- Reflection invariance of the Gibbs weight.  This is a property of the
lattice geometry, so it is carried as a hypothesis and discharged by each
concrete system. -/
def ReflInvariant (G : GaugeData N Edge Plaq) : Prop :=
  ∀ U : Config N Edge, boltz G (reflConfig G U) = boltz G U

/-- Under reflection invariance the reflection is a bijection of configurations
that preserves the weight, so it preserves the partition function. -/
theorem partition_reflInvariant (G : GaugeData N Edge Plaq) (h : ReflInvariant G) :
    ∑ U : Config N Edge, boltz G (reflConfig G U) = partition G := by
  unfold partition
  exact Finset.sum_congr rfl fun U _ => h U

/-! ## Non-vacuity -/

/-- A concrete inhabitant: two edges exchanged by the reflection, one plaquette
whose boundary is both edges, and the constant weight `1`.  Minimal on purpose
— it shows `GaugeData` is inhabited and `ReflInvariant` is satisfiable at
`N ≥ 2`; it is not a physically interesting lattice, and the box instance is
registered for O-3b. -/
def minimalSystem (N : ℕ) : GaugeData N (Fin 2) (Fin 1) where
  inc := fun _ _ => 1
  weight := fun _ => 1
  weight_pos := fun _ => one_pos
  refl := fun e => if e = 0 then 1 else 0
  refl_refl := by decide

theorem minimalSystem_reflInvariant (N : ℕ) [NeZero N] :
    ReflInvariant (minimalSystem N) := by
  intro U
  unfold boltz minimalSystem
  simp

/-- The configuration space of the witness is genuinely nontrivial at `N ≥ 2`:
two configurations differ, so the system is not the one-point theory. -/
theorem minimalSystem_config_nontrivial (N : ℕ) [NeZero N] (h : 1 < N) :
    ∃ U V : Config N (Fin 2), U ≠ V := by
  refine ⟨fun _ => 0, fun _ => 1, ?_⟩
  intro hUV
  have h0 : (0 : ZMod N) = 1 := congrFun hUV 0
  have : (1 : ZMod N) ≠ 0 := by
    haveI : Fact (1 < N) := ⟨h⟩
    exact one_ne_zero
  exact this h0.symm

/-- The reflection of the witness is not the identity: it genuinely exchanges
the two edges, so the involution is nontrivial. -/
theorem minimalSystem_refl_ne_id (N : ℕ) :
    (minimalSystem N).refl ≠ id := by
  intro h
  have := congrFun h 0
  simp [minimalSystem] at this

end YangMills.OS
