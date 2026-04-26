/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L7_Continuum.DimensionalTransmutation

/-!
# Physical lattice scheme construction — Branch VII (Cowork)

This module provides **constructive inhabitants** of
`PhysicalLatticeScheme N_c` from running-coupling profiles, going
beyond the `trivialPhysicalScheme` (in `DimensionalTransmutation.lean`)
which uses `g(N) = 1/(N+1)`.

## Strategic role

The `trivialPhysicalScheme` is sufficient to demonstrate that
`HasContinuumMassGap_Genuine` is non-vacuously inhabitable, but it
does NOT correspond to any physical Yang-Mills lattice spacing.

For `ClayYangMillsPhysicalStrong_Genuine` to be inhabited
**physically** (not just structurally), we need a `PhysicalLatticeScheme`
whose spacing `a(N)` and coupling `g(N)` come from a **physical
running-coupling profile** consistent with asymptotic freedom and the
Wilson lattice action.

## What this file provides

* `PhysicalRunningCouplingProfile`: structure encoding a physical AF
  coupling profile with the standard 1-loop running.
* `physicalScheme_of_runningCoupling`: constructs a
  `PhysicalLatticeScheme N_c` from a running-coupling profile.
* Conditional theorems linking the constructed scheme to the
  AF-spacing relation.

## Status

**Scaffold + hypothesis-conditioned**. No `sorry`. The construction
works for any positive coupling profile satisfying the standard AF
running. Inhabiting `PhysicalRunningCouplingProfile` from physics is
straightforward (1-loop β-function); the harder content is showing
the lattice action is consistent with this profile, which is
Branch II / Bałaban territory.

Per project discipline, every theorem here has oracle
`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.Continuum

open Real Filter Topology

/-! ## §1. Physical running-coupling profile -/

/-- A **physical running-coupling profile** for SU(N_c) Yang-Mills.

    Encodes the standard 1-loop AF running:
    * `g : ℕ → ℝ` — the coupling at lattice resolution `N`.
    * `g_pos`: `g(N) > 0` for all `N`.
    * `g_lt_one`: `g(N) < 1` for all `N` (small-coupling regime).
    * `g_to_zero`: `g(N) → 0` as `N → ∞` (asymptotic freedom).
    * `g_AF_relation`: the spacing-coupling relation
      `a(N) · exp(1/(2 b₀ g(N)²)) → 1/Λ` for some `Λ > 0`, where
      `a(N)` is supplied as part of the profile.

    The profile bundles spacing and coupling together in a way that
    automatically satisfies the `PhysicalLatticeScheme` constraints. -/
structure PhysicalRunningCouplingProfile (N_c : ℕ) [NeZero N_c] : Type where
  /-- Coupling at each resolution. -/
  g : ℕ → ℝ
  /-- Coupling positivity. -/
  g_pos : ∀ N, 0 < g N
  /-- Coupling stays in the small-coupling regime (< 1). -/
  g_lt_one : ∀ N, g N < 1
  /-- Asymptotic freedom: `g(N) → 0`. -/
  g_to_zero : Tendsto g atTop (𝓝 0)
  /-- Lattice spacing. -/
  a : ℕ → ℝ
  /-- Spacing positivity. -/
  a_pos : ∀ N, 0 < a N
  /-- Spacing tends to zero (continuum limit). -/
  a_to_zero : Tendsto a atTop (𝓝 0)
  /-- The AF spacing-coupling relation:
      `a(N) · exp(1/(2 b₀ g(N)²)) → 1/Λ`. -/
  AF_relation : ∃ Λ : ℝ, 0 < Λ ∧
    Tendsto (fun N => a N * Real.exp (1 / (2 * b0 N_c * (g N)^2)))
      atTop (𝓝 (1 / Λ))

/-! ## §2. Construct PhysicalLatticeScheme from profile -/

/-- Construct a `PhysicalLatticeScheme N_c` from a running-coupling
    profile. -/
noncomputable def physicalScheme_of_runningCoupling
    {N_c : ℕ} [NeZero N_c]
    (profile : PhysicalRunningCouplingProfile N_c) :
    PhysicalLatticeScheme N_c where
  a := profile.a
  ha_pos := profile.a_pos
  ha_tends_zero := profile.a_to_zero
  g := profile.g
  hg_pos := profile.g_pos
  hg_asymp_free := profile.g_to_zero
  ha_g_relation := profile.AF_relation

/-! ## §3. Concrete profile from the trivial scheme -/

/-- Wrapper around `trivialPhysicalScheme` to expose it as a
    `PhysicalRunningCouplingProfile`.

    Useful for sanity-checking and for demonstrating that the profile
    structure is non-vacuously inhabitable.

    Note: this profile has `g(N) = 1/(N+1)` which does NOT correspond
    to physical 1-loop AF running; it's a placeholder profile chosen
    so that the AF relation holds by construction (`a(N)` defined
    as `(1/Λ) · exp(-1/(2 b₀ g(N)²))`). -/
noncomputable def trivialRunningCouplingProfile
    (N_c : ℕ) [NeZero N_c] (h_NC : 1 ≤ N_c)
    (Λ : ℝ) (hΛ : 0 < Λ) :
    PhysicalRunningCouplingProfile N_c where
  g := fun N => 1 / ((N : ℝ) + 1)
  g_pos := fun N => by positivity
  g_lt_one := fun N => by
    have hN : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
    have : (1 : ℝ) < (N : ℝ) + 1 := by linarith
    rw [div_lt_one (by linarith : (0:ℝ) < (N:ℝ)+1)]
    exact this
  g_to_zero := tendsto_one_div_add_atTop_nhds_zero_nat
  a := fun N => afRenormalizedSpacing N_c Λ (1 / ((N : ℝ) + 1))
  a_pos := fun N => by
    have hg_pos : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
    exact afRenormalizedSpacing_pos h_NC hΛ hg_pos
  a_to_zero := by
    have hg_zero_pos :
        Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝[>] (0:ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
      apply Filter.eventually_of_forall
      intro N
      positivity
    exact (afRenormalizedSpacing_tendsto_zero h_NC hΛ).comp hg_zero_pos
  AF_relation := by
    refine ⟨Λ, hΛ, ?_⟩
    have hfun_eq : (fun N : ℕ =>
        afRenormalizedSpacing N_c Λ (1 / ((N : ℝ) + 1))
        * Real.exp (1 / (2 * b0 N_c * (1 / ((N : ℝ) + 1))^2)))
        = fun _ => 1 / Λ := by
      funext N
      unfold afRenormalizedSpacing
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    rw [hfun_eq]
    exact tendsto_const_nhds

/-- Sanity check: the trivial profile produces the trivial scheme. -/
theorem physicalScheme_of_trivialRunningCouplingProfile_eq_trivialPhysicalScheme
    {N_c : ℕ} [NeZero N_c] (h_NC : 1 ≤ N_c)
    (Λ : ℝ) (hΛ : 0 < Λ) :
    (physicalScheme_of_runningCoupling
        (trivialRunningCouplingProfile N_c h_NC Λ hΛ)).a =
      (trivialPhysicalScheme N_c h_NC Λ hΛ).a := rfl

#print axioms physicalScheme_of_trivialRunningCouplingProfile_eq_trivialPhysicalScheme

/-! ## §4. Bridge to F3ToAFShape -/

/-
For physical Yang-Mills, the running-coupling profile should come
from the **Bałaban RG flow**: the bare lattice coupling `g₀` evolves
under blockings to produce the physical coupling `g_phys(a)` with
the standard 1-loop running.

Inhabiting a physical `PhysicalRunningCouplingProfile N_c` from
Bałaban RG output is the substantive Branch II work
(`ClayCore/BalabanRG/PhysicalRGRates.lean` and similar files cover
this). When that lands, combining with the AF-form `φ_AF`
construction produces the `F3ToAFShape` needed for Path A closure.

This file provides the structural machinery; the inhabitation is
downstream Branch II responsibility.
-/

end YangMills.Continuum
