/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson

O-3b(ii): the geometric half of reflection positivity — a splitting of the
configuration space across the reflection plane, and the theorem that a
splitting with a PSD crossing kernel yields a positive Osterwalder-Seiler
pairing.

Charter: docs/O-BRIDGE-CHARTER.md, AMENDMENT 6.
-/

import Mathlib
import YangMills.OS.ZNSubstrate
import YangMills.OS.PSDKernel

/-!
# O-3b(ii) — splitting across the plane, and reflection positivity

## What was missing

O-3a carries `ReflInvariant`: the Gibbs weight is unchanged by the reflection.
That is strictly weaker than what reflection positivity needs.  The argument
needs the configuration space to **split** across the plane —
`Config ≃ Half × Half` with the reflection acting as the swap — and the weight
to **factorise** as `w(x) · w(y) · K(x,y)`, with `w` the half-space factor and
`K` the contribution of the plaquettes that straddle the plane.  This module
formulates that as data and proves what it buys.

## What is proved

`osPairing_eq_kernelForm`: the Osterwalder--Seiler pairing of an observable of
one half against its reflection is *exactly* the quadratic form of the kernel
`w(x) · K(x,y) · w(y)`.  Combining with O-3b(i):

* `isPSDKernel_osKernel` — if the crossing kernel is a non-negative character
  combination then the full kernel is PSD, the half-space factors being
  absorbed by `isCharCombo_diagConj`;
* `osPairing_nonneg` — hence the pairing is a non-negative real.  That is
  reflection positivity.

## What is carried as hypothesis, and why

The splitting itself.  Producing it for a named lattice is geometric
bookkeeping: one must exhibit the half-space edge sets, check that the
reflection exchanges them, and sort the plaquettes into the three classes.
Carrying it as data means the analytic content can be stated and proved once,
and each concrete lattice discharges the geometry separately.  The witness
below discharges it for the minimal system of O-3a — which is honest about
being minimal: it shows the structure is inhabited and the whole chain fires
end to end, not that any physically interesting lattice has been treated.

It is still **not** claimed that the Wilson weight is a non-negative character
combination.  That is O-3b(iii) and it is where the physics enters.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.OS

set_option linter.unusedSectionVars false

open Finset

variable {N : ℕ} [NeZero N] {Edge Plaq : Type*}
variable [Fintype Edge] [DecidableEq Edge] [Fintype Plaq]

/-- A splitting of the configuration space across the reflection plane: an
identification `Config ≃ Half × Half` under which the reflection is the swap,
together with the factorisation of the Gibbs weight into two half-space factors
and a crossing kernel. -/
structure ReflectionSplitting (G : GaugeData N Edge Plaq) (Half : Type*) where
  /-- The identification of a configuration with its pair of halves. -/
  split : Config N Edge ≃ (Half × Half)
  /-- Under it the reflection is exactly the swap. -/
  split_refl : ∀ U, split (reflConfig G U) = ((split U).2, (split U).1)
  /-- The half-space factor of the weight. -/
  w : Half → ℝ
  /-- It is strictly positive. -/
  w_pos : ∀ h, 0 < w h
  /-- The crossing kernel: the contribution of the plaquettes straddling the
  plane. -/
  K : Half → Half → ℂ
  /-- The factorisation of the Gibbs weight across the plane. -/
  factor : ∀ U, (boltz G U : ℂ)
    = (w (split U).1 : ℂ) * (w (split U).2 : ℂ) * K (split U).1 (split U).2

variable {G : GaugeData N Edge Plaq} {Half : Type*} [Fintype Half] [DecidableEq Half]

/-- The kernel whose quadratic form the Osterwalder--Seiler pairing is: the
crossing kernel conjugated by the half-space factors. -/
noncomputable def osKernel (S : ReflectionSplitting G Half) : Half → Half → ℂ :=
  fun x y => (S.w x : ℂ) * S.K x y * (S.w y : ℂ)

/-- The Osterwalder--Seiler pairing of an observable of one half against its
reflection.  `F` is a function of a single half-space configuration; the sum
runs over all configurations of the whole system. -/
noncomputable def osPairing (S : ReflectionSplitting G Half) (F : Half → ℂ) : ℂ :=
  ∑ U : Config N Edge,
    (boltz G U : ℂ) * (starRingEnd ℂ) (F (S.split U).1) * F (S.split U).2

/-- **The identity that does the work.**  The pairing is exactly the quadratic
form of the conjugated crossing kernel.  Everything else in this module is a
corollary of it together with O-3b(i). -/
theorem osPairing_eq_kernelForm (S : ReflectionSplitting G Half) (F : Half → ℂ) :
    osPairing S F = kernelForm (osKernel S) F := by
  unfold osPairing kernelForm osKernel
  -- reindex the sum over configurations by the splitting
  rw [← Equiv.sum_comp S.split.symm
    (fun U => (boltz G U : ℂ) * (starRingEnd ℂ) (F (S.split U).1) * F (S.split U).2)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun y _ => ?_
  have hsplit : S.split (S.split.symm (x, y)) = (x, y) := S.split.apply_symm_apply (x, y)
  rw [S.factor (S.split.symm (x, y)), hsplit]
  ring

/-- If the crossing kernel is a non-negative character combination then the
kernel of the pairing is positive semidefinite: the half-space factors are
absorbed by conjugation with a positive diagonal. -/
theorem isPSDKernel_osKernel {ι : Type*} [Fintype ι] {c : ι → ℝ} {φ : ι → Half → ℂ}
    (S : ReflectionSplitting G Half) (h : IsCharCombo c φ S.K) :
    IsPSDKernel (osKernel S) :=
  isPSDKernel_of_charCombo (isCharCombo_diagConj h S.w)

/-- **Reflection positivity.**  With a splitting whose crossing kernel is a
non-negative character combination, the Osterwalder--Seiler pairing of any
observable of one half against its reflection is a non-negative real. -/
theorem osPairing_nonneg {ι : Type*} [Fintype ι] {c : ι → ℝ} {φ : ι → Half → ℂ}
    (S : ReflectionSplitting G Half) (h : IsCharCombo c φ S.K) (F : Half → ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧ osPairing S F = (r : ℂ) := by
  rw [osPairing_eq_kernelForm]
  exact isPSDKernel_osKernel S h F

/-! ## Non-vacuity: the chain fires end to end on the minimal system -/

/-- The splitting of the minimal system of O-3a: its two edges are the two
halves, and the reflection exchanges them by construction. -/
noncomputable def minimalSplitting (N : ℕ) [NeZero N] :
    ReflectionSplitting (minimalSystem N) (ZMod N) where
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
    simp [reflConfig, minimalSystem]
  w := fun _ => 1
  w_pos := fun _ => one_pos
  K := fun _ _ => 1
  factor := by
    intro U
    simp [boltz, minimalSystem]

/-- The crossing kernel of the minimal splitting is a non-negative character
combination — the constant one, with a single index. -/
theorem minimalSplitting_charCombo (N : ℕ) [NeZero N] :
    IsCharCombo (fun _ : Unit => (1 : ℝ)) (fun _ => fun _ : ZMod N => (1 : ℂ))
      (minimalSplitting N).K where
  coeff_nonneg := fun _ => zero_le_one
  eq := by intro x y; simp [minimalSplitting]

/-- **The chain fires.**  Reflection positivity holds for the minimal system.
The physics content is nil — the weight is constant — but the statement is the
genuine conclusion of the genuine chain, obtained by discharging a splitting
and a character combination rather than by assuming a pairing. -/
theorem minimalSplitting_reflectionPositive (N : ℕ) [NeZero N] (F : ZMod N → ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧ osPairing (minimalSplitting N) F = (r : ℂ) :=
  osPairing_nonneg _ (minimalSplitting_charCombo N) F

end YangMills.OS
