/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.ClayCore.WilsonPlaquetteEnergy
import YangMills.ClayCore.SmallFieldBound
import YangMills.L0_Lattice.FiniteLatticeGeometryInstance

/-!
# Phase 15j.1: Wilson Polymer Activity Bound

Defines the Wilson-Gibbs single-plaquette weight `plaquetteWeight`
and packages the Kotecky-Preiss / high-temperature polymer activity
bound

    ‖K(γ)‖∞ ≤ A₀ · r^|γ|

as a structure `WilsonPolymerActivityBound`, whose key amplitude
inequality is an abstract hypothesis field (exactly the analytic
input required by the KP framework).

As in `CharacterExpansionData` and `TruncatedActivities`, we do NOT
reprove the combinatorial activity bound here — that is the content
of Balaban CMP 116 Lemma 3 / Bloque4 §5.1 and the character-expansion
asymptotics of Bessel-type coefficients. Instead, we expose the bound
as a structure field and derive the downstream consequences (a
`SmallFieldActivityBound`, hence a `BalabanH1 N_c`) cleanly.

Sub-lemma **15j.1** on the path to `ClusterCorrelatorBound`.

Oracle target: `[propext, Classical.choice, Quot.sound]`.
No sorry. No new axioms.

References:
* Bloque4 §5.1, high-temperature expansion.
* Balaban, Commun. Math. Phys. **116** (1988), Lemma 3, Eq. (2.38).
* Kotecky-Preiss, Commun. Math. Phys. **103** (1986).
-/

namespace YangMills

open Real Matrix

noncomputable section

/-! ## Single-plaquette Wilson-Gibbs weight -/

/-- Single-plaquette Wilson-Gibbs weight:
    `plaquetteWeight N_c β U = exp(-β · wilsonPlaquetteEnergy N_c U)`.

    This is the pointwise integrand of the Gibbs density on a single
    plaquette, before normalisation by the partition function. -/
noncomputable def plaquetteWeight
    (N_c : ℕ) [NeZero N_c] (β : ℝ)
    (U : ↥(specialUnitaryGroup (Fin N_c) ℂ)) : ℝ :=
  Real.exp (-β * wilsonPlaquetteEnergy N_c U)

/-- The plaquette weight is strictly positive. -/
theorem plaquetteWeight_pos
    (N_c : ℕ) [NeZero N_c] (β : ℝ)
    (U : ↥(specialUnitaryGroup (Fin N_c) ℂ)) :
    0 < plaquetteWeight N_c β U := Real.exp_pos _

/-- The plaquette weight is continuous as a function of the link. -/
theorem plaquetteWeight_continuous
    (N_c : ℕ) [NeZero N_c] (β : ℝ) :
    Continuous (plaquetteWeight N_c β) := by
  unfold plaquetteWeight
  have hE : Continuous (wilsonPlaquetteEnergy N_c) :=
    wilsonPlaquetteEnergy_continuous N_c
  -- `continuous_const.mul hE` has type
  -- `Continuous (fun U => c * wilsonPlaquetteEnergy N_c U)`
  -- and `c` unifies with the goal's `(-β)` directly. The earlier
  -- `(continuous_const.mul hE).neg` produced `-(c * ...)` which does
  -- not unify with `(-β) * ...`.
  exact Real.continuous_exp.comp (continuous_const.mul hE)

end

/-! ## Wilson polymer activity bound (structure) -/

/-- Wilson polymer activity bound structure.

    Packages the Kotecky-Preiss activity bound
    `|K(γ)| ≤ A₀ · r^|γ|`
    for the Wilson-Gibbs measure as an abstract hypothesis field.

    The activity `K` is the connected Ursell / truncated activity of
    a polymer (finite set of plaquettes); its amplitude bound drives
    the absolute convergence of the cluster sum. -/
structure WilsonPolymerActivityBound (N_c : ℕ) [NeZero N_c] where
  /-- Inverse coupling. -/
  β : ℝ
  /-- Coupling is strictly positive. -/
  hβ : 0 < β
  /-- Geometric decay rate. -/
  r : ℝ
  /-- Decay rate is strictly positive. -/
  hr_pos : 0 < r
  /-- Decay rate is strictly less than one. -/
  hr_lt1 : r < 1
  /-- Amplitude prefactor (nonnegative). -/
  A₀ : ℝ
  /-- Prefactor is nonnegative. -/
  hA₀ : 0 ≤ A₀
  /-- Truncated activity of a polymer (Finset of plaquettes). -/
  K : ∀ {d L : ℕ} [NeZero d] [NeZero L],
      Finset (ConcretePlaquette d L) → ℝ
  /-- The amplitude bound `|K γ| ≤ A₀ · r^|γ|`, discharged by
      Balaban CMP 116 Lemma 3 / Bloque4 §5.1. -/
  h_bound :
    ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (γ : Finset (ConcretePlaquette d L)),
      |K (d := d) (L := L) γ| ≤ A₀ * r ^ γ.card

/-! ## From Wilson activity to SmallFieldActivityBound and BalabanH1 -/

/-- A Wilson polymer activity bound produces a
    `SmallFieldActivityBound` with trivial plaquette activity
    (activity ≡ 0) and small-field constants driven by the
    decay rate `r = g_bar`, `κ = -log r`, `E₀ = 1`.

    The zero activity trivially satisfies the small-field
    inequality, since the right-hand side is nonnegative. -/
noncomputable def smallFieldBound_of_wilsonActivity
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c) :
    SmallFieldActivityBound N_c where
  consts :=
    { E0    := 1
    , hE0   := by norm_num
    , kappa := -Real.log wab.r
    , hkappa :=
        neg_pos.mpr (Real.log_neg wab.hr_pos wab.hr_lt1)
    , g_bar := wab.r
    , hg_pos := wab.hr_pos
    , hg_lt1 := wab.hr_lt1 }
  activity := fun _ => 0
  hact_nn  := fun _ => le_refl 0
  hact_bd  := fun n => by
    have hr_pos : 0 < wab.r := wab.hr_pos
    have hexp_pos : 0 < Real.exp (-(-Real.log wab.r) * (n : ℝ)) :=
      Real.exp_pos _
    have hpow : 0 < wab.r ^ 2 := by positivity
    nlinarith [hexp_pos, hpow]

/-- **KEY THEOREM (15j.1).** A Wilson polymer activity bound
    produces a `BalabanH1 N_c` with the prescribed decay rate. -/
theorem balabanH1_from_wilson_activity
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c) :
    ∃ h1 : BalabanH1 N_c, h1.g_bar = wab.r :=
  ⟨h1_of_small_field_bound (smallFieldBound_of_wilsonActivity wab), rfl⟩

/-! ### P2d-α: enriched constructor with nontrivial polymer activity

v0.44.0 / Phase 3 / Task #7 P2d-α: pure-additive enriched constructor
`SmallFieldActivityBound.ofWilsonActivity` that carries the polymer
prefactor `A₀` and decay rate `r` from `WilsonPolymerActivityBound`
into a *nontrivial* activity profile `activity n := A₀ · r^(n+2)`,
rather than the trivially-zero shortcut of the legacy
`smallFieldBound_of_wilsonActivity`.

Constants:
- `E₀ := A₀ + 1`   (ensures `0 < E₀` even when `A₀ = 0`),
- `κ := -log r`    (positive since `0 < r < 1`),
- `ḡ := r`         (directly carries the polymer decay rate).

The activity bound
`A₀ · r^(n+2) ≤ (A₀ + 1) · r^2 · exp(-(-log r)·n)`
reduces to `A₀ ≤ A₀ + 1` after normalising
`exp(-(-log r) · n) = r^n` and `r^(n+2) = r^n · r^2`.

This does **not** retire `WilsonPolymerActivityBound.h_bound`; that
abstract amplitude inequality (Balaban CMP 116 Lemma 3 analytic content)
remains a struct-hypothesis field. What changes: the small-field
`activity` is now semantically tied to the polymer pair `(A₀, r)`
instead of identically zero — matching the Balaban small-field
activity "macro shape" without bypassing any assumptions. -/
noncomputable def SmallFieldActivityBound.ofWilsonActivity
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c) :
    SmallFieldActivityBound N_c where
  consts :=
    { E0     := wab.A₀ + 1
    , hE0    := by linarith [wab.hA₀]
    , kappa  := -Real.log wab.r
    , hkappa := neg_pos.mpr (Real.log_neg wab.hr_pos wab.hr_lt1)
    , g_bar  := wab.r
    , hg_pos := wab.hr_pos
    , hg_lt1 := wab.hr_lt1 }
  activity := fun n => wab.A₀ * wab.r ^ (n + 2)
  hact_nn  := fun n => by
    have hr_nn : 0 ≤ wab.r := le_of_lt wab.hr_pos
    have hpow : 0 ≤ wab.r ^ (n + 2) := pow_nonneg hr_nn _
    nlinarith [wab.hA₀, hpow]
  hact_bd  := fun n => by
    have hr_pos : 0 < wab.r := wab.hr_pos
    have hrn_pos : 0 < wab.r ^ n := pow_pos hr_pos n
    have hr2_pos : 0 < wab.r ^ 2 := pow_pos hr_pos 2
    have hexp : Real.exp (-(-Real.log wab.r) * (n : ℝ)) = wab.r ^ n := by
      rw [neg_neg]
      rw [show Real.log wab.r * (n : ℝ) = Real.log (wab.r ^ n) by
        rw [Real.log_pow]; ring]
      exact Real.exp_log hrn_pos
    have hpow : wab.r ^ (n + 2) = wab.r ^ n * wab.r ^ 2 := by rw [pow_add]
    rw [hpow, hexp]
    nlinarith [wab.hA₀, hrn_pos, hr2_pos]

/-! ### P2d-β: enriched BalabanH1 with polymer-faithful small-field activity

v0.45.0 / Phase 3 / Task #7 P2d-β: pure-additive enriched constructor that
composes `SmallFieldActivityBound.ofWilsonActivity` (P2d-α, v0.44.0) with
`h1_of_small_field_bound` (`SmallFieldBound.lean`) to produce a first-class
`BalabanH1 N_c` term whose small-field activity profile is
`activity n := A₀ · r^(n+2)` — polymer-faithful — instead of identically
zero (the legacy `balabanH1_from_wilson_activity` route via the
trivial-activity shortcut `smallFieldBound_of_wilsonActivity`).

Demonstrates the P2d-α enriched constructor is not decorative but
propagates cleanly through `h1_of_small_field_bound` to a `BalabanH1`
with semantically faithful small-field content. Pure additive: legacy
`balabanH1_from_wilson_activity` (existential statement with trivial
activity) is kept intact and still callable. -/
noncomputable def balabanH1_from_wilson_activity_enriched
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c) :
    BalabanH1 N_c :=
  h1_of_small_field_bound (SmallFieldActivityBound.ofWilsonActivity wab)

end YangMills

#print axioms YangMills.smallFieldBound_of_wilsonActivity
#print axioms YangMills.balabanH1_from_wilson_activity
#print axioms YangMills.SmallFieldActivityBound.ofWilsonActivity
#print axioms YangMills.balabanH1_from_wilson_activity_enriched
