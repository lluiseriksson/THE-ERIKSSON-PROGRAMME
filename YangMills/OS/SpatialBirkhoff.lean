/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson

O-3g: the SECOND elementary route, and where it stops.

O-3f (`YangMills/OS/SpatialExtent.lean`) proved that row-sum normalisation stops
producing the vacuum as soon as a spatial coupling is switched on.  The standard
replacement, when constant row sums fail, is the Hilbert projective metric and
the Birkhoff contraction coefficient.  This module proves that replacement is
blind to the coupling and degenerates in the volume.

Charter: docs/O-BRIDGE-CHARTER.md.
-/

import Mathlib
import YangMills.OS.SpatialExtent

/-!
# O-3g — the Hilbert/Birkhoff route is `γ`-blind and volume-degenerate

## What this module proves

When constant row sums fail, the textbook replacement is the **Hilbert projective
metric**: a strictly positive kernel contracts it, the contraction factor is
`tanh (Δ / 4)` where `Δ` is the projective diameter, and that factor bounds the
subdominant spectral ratio.  It is the natural second attempt, and it is what a
reader of O-3f would try next.

Two facts kill it here.

**BLINDNESS** (`crossRatio_sourceWeighted`).  The projective cross-ratio is
invariant under multiplying a kernel by *any* nowhere-zero function of the
**source** alone.  The coupled kernel of O-3f is exactly such a product, so the
Hilbert metric assigns the interacting and the non-interacting kernels the same
diameter: the route cannot see `γ` at all.  This is not a feature of the
particular weight — it holds for every source-only weight, at every spatial
extent.

**VOLUME DEGENERATION** (`crossRatio_const`, `projDiameter_ge`,
`birkhoff_bound_ge`).  Two constant configurations realise the cross-ratio
`exp (4 β L)`, so every admissible projective diameter is at least `4 β L` and
every Birkhoff contraction factor obtainable this way is at least
`tanh (β L)`, which by `one_sub_tanh_le` sits within `2 exp (-2 β L)` of the
trivial bound `1`.

Together: at the one place where the truth is known — the decoupled kernel,
whose subdominant ratio O-3f computes to be exactly `tanh β`, independent of
`L` — this route already returns `tanh (β L)` instead.  The degeneration is the
method's, not the model's.

## What is NOT claimed

That no contraction argument can work; that the vacuum fails to exist (a positive
kernel on a finite set has a Perron vector); that a volume-uniform gap is false
for the coupled system.  The last is a separate, *measured and unproved* matter
recorded in `docs/O-LANE-CONTINUATION-20260728.md`.

Nothing here concerns `SU(N)`, the continuum limit, or the Clay problem.

Oracle target: `[propext, Classical.choice, Quot.sound]`.  No sorry, no axioms.
-/

namespace YangMills.OS

set_option linter.unusedSectionVars false

/-! ## §1  A closed form for `tanh`, and the two facts we need from it -/

/-- `tanh x = 1 − 2 / (exp (2x) + 1)`.  Everything this module needs about
`tanh` — monotonicity and the distance to `1` — reads off this form. -/
theorem tanh_eq_one_sub (x : ℝ) :
    Real.tanh x = 1 - 2 / (Real.exp (2 * x) + 1) := by
  have hx : (0:ℝ) < Real.exp x := Real.exp_pos x
  have hne : Real.exp x ≠ 0 := ne_of_gt hx
  have h2 : (0:ℝ) < Real.exp (2 * x) + 1 := by positivity
  have hxx : Real.exp (2 * x) = Real.exp x * Real.exp x := by
    rw [show (2:ℝ) * x = x + x by ring, Real.exp_add]
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, Real.exp_neg, hxx]
  rw [hxx] at h2
  field_simp
  ring

/-- `tanh` is monotone. -/
theorem tanh_le_tanh {x y : ℝ} (h : x ≤ y) : Real.tanh x ≤ Real.tanh y := by
  rw [tanh_eq_one_sub, tanh_eq_one_sub]
  have hx : (0:ℝ) < Real.exp (2 * x) + 1 := by positivity
  have hy : (0:ℝ) < Real.exp (2 * y) + 1 := by positivity
  have hxy : Real.exp (2 * x) + 1 ≤ Real.exp (2 * y) + 1 := by
    have := Real.exp_le_exp.mpr (by linarith : 2 * x ≤ 2 * y)
    linarith
  have hkey : 2 / (Real.exp (2 * y) + 1) ≤ 2 / (Real.exp (2 * x) + 1) := by
    rw [div_le_div_iff₀ hy hx]
    linarith
  linarith

/-- **The distance to the trivial bound.**  `1 − tanh x ≤ 2 e^{-2x}`.  Applied at
`x = β L` this says the factor `tanh (β L)` — which by `birkhoff_bound_ge` is a
lower bound for every contraction factor this route can produce — is itself
exponentially close to the trivial bound `1` in the volume. -/
theorem one_sub_tanh_le (x : ℝ) :
    1 - Real.tanh x ≤ 2 * Real.exp (-(2 * x)) := by
  rw [tanh_eq_one_sub]
  have h1 : (0:ℝ) < Real.exp (2 * x) := Real.exp_pos _
  have h2 : (0:ℝ) < Real.exp (2 * x) + 1 := by linarith
  have hkey : 2 / (Real.exp (2 * x) + 1) ≤ 2 / Real.exp (2 * x) := by
    rw [div_le_div_iff₀ h2 h1]
    linarith
  have hinv : 2 / Real.exp (2 * x) = 2 * Real.exp (-(2 * x)) := by
    rw [Real.exp_neg]
    field_simp
  linarith [hkey, hinv]

/-! ## §2  The projective cross-ratio -/

/-- The projective cross-ratio of a kernel at four points.  The Hilbert
projective diameter of a strictly positive kernel is the supremum of its
logarithm, and the Birkhoff contraction factor is `tanh (diameter / 4)`. -/
noncomputable def crossRatio {α : Type*} (A : α → α → ℝ) (σ σ' τ τ' : α) : ℝ :=
  A σ τ * A σ' τ' / (A σ τ' * A σ' τ)

/-! ## §3  BLINDNESS — no source-only weight is visible to the metric -/

/-- A kernel multiplied by a weight depending on the **source** only.  The
coupled kernel of O-3f is the case `w = spatialWeight γ`, `L = 2`. -/
noncomputable def sourceWeighted {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ)
    (σ τ : Fin L → Fin 2) : ℝ :=
  w σ * spatialKernel β σ τ

/-- **THE BLINDNESS THEOREM.**  The projective cross-ratio does not change when
the kernel is multiplied by any nowhere-zero function of the source.  The weight
appears once in the numerator and once in the denominator, at the same two
configurations, and cancels identically. -/
theorem crossRatio_sourceWeighted {L : ℕ} (w : (Fin L → Fin 2) → ℝ)
    (hw : ∀ σ, w σ ≠ 0) (β : ℝ) (σ σ' τ τ' : Fin L → Fin 2) :
    crossRatio (sourceWeighted w β) σ σ' τ τ'
      = crossRatio (spatialKernel β) σ σ' τ τ' := by
  unfold crossRatio sourceWeighted
  rw [show w σ * spatialKernel β σ τ * (w σ' * spatialKernel β σ' τ')
        = w σ * w σ' * (spatialKernel β σ τ * spatialKernel β σ' τ') by ring,
      show w σ * spatialKernel β σ τ' * (w σ' * spatialKernel β σ' τ)
        = w σ * w σ' * (spatialKernel β σ τ' * spatialKernel β σ' τ) by ring]
  exact mul_div_mul_left _ _ (mul_ne_zero (hw σ) (hw σ'))

theorem spatialWeight_pos (γ : ℝ) (σ : Fin 2 → Fin 2) : 0 < spatialWeight γ σ :=
  z2Bond_pos γ _ _

theorem coupledKernel_eq_sourceWeighted (β γ : ℝ) :
    coupledKernel β γ = sourceWeighted (spatialWeight γ) β := rfl

/-- **The route cannot see the coupling.**  The coupled kernel of O-3f and the
decoupled kernel have the *same* projective cross-ratio at every four
configurations, for every `γ`. -/
theorem crossRatio_coupledKernel (β γ : ℝ) (σ σ' τ τ' : Fin 2 → Fin 2) :
    crossRatio (coupledKernel β γ) σ σ' τ τ'
      = crossRatio (spatialKernel β) σ σ' τ τ' := by
  rw [coupledKernel_eq_sourceWeighted]
  exact crossRatio_sourceWeighted _ (fun σ => ne_of_gt (spatialWeight_pos γ σ)) β σ σ' τ τ'

/-! ## §4  VOLUME DEGENERATION — an explicit cross-ratio witness -/

/-- `exp x ^ n = exp (n x)`, proved here rather than searched for by name. -/
theorem exp_pow_eq (x : ℝ) (n : ℕ) : Real.exp x ^ n = Real.exp (n * x) := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih, ← Real.exp_add]
      congr 1
      push_cast
      ring

/-- The constant configuration at spatial extent `L`. -/
noncomputable def cfgConst (L : ℕ) (a : Fin 2) : Fin L → Fin 2 := fun _ => a

theorem spatialKernel_const_same (β : ℝ) (L : ℕ) (a : Fin 2) :
    spatialKernel β (cfgConst L a) (cfgConst L a) = Real.exp β ^ L := by
  simp only [spatialKernel, cfgConst]
  rw [Finset.prod_congr rfl fun j _ => z2Bond_same β a, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

theorem spatialKernel_const_diff (β : ℝ) (L : ℕ) {a b : Fin 2} (h : a ≠ b) :
    spatialKernel β (cfgConst L a) (cfgConst L b) = Real.exp (-β) ^ L := by
  simp only [spatialKernel, cfgConst]
  rw [Finset.prod_congr rfl fun j _ => z2Bond_ne h β, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-- **THE WITNESS.**  At the all-`0` and all-`1` configurations the cross-ratio
of the decoupled kernel is exactly `exp (4 β L)`: it grows linearly in the
volume in the exponent. -/
theorem crossRatio_const (β : ℝ) (L : ℕ) :
    crossRatio (spatialKernel β) (cfgConst L 0) (cfgConst L 1)
        (cfgConst L 0) (cfgConst L 1)
      = Real.exp (4 * β * L) := by
  unfold crossRatio
  rw [spatialKernel_const_same, spatialKernel_const_same,
    spatialKernel_const_diff β L (by decide : (0:Fin 2) ≠ 1),
    spatialKernel_const_diff β L (by decide : (1:Fin 2) ≠ 0)]
  rw [exp_pow_eq, exp_pow_eq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_sub]
  congr 1
  ring

/-- **THE WALL, first form.**  Any number that bounds the logarithm of every
cross-ratio — that is, any admissible Hilbert projective diameter for the
decoupled kernel at extent `L` — is at least `4 β L`. -/
theorem projDiameter_ge {β : ℝ} (L : ℕ) (D : ℝ)
    (hD : ∀ σ σ' τ τ' : Fin L → Fin 2,
      Real.log (crossRatio (spatialKernel β) σ σ' τ τ') ≤ D) :
    4 * β * L ≤ D := by
  have h := hD (cfgConst L 0) (cfgConst L 1) (cfgConst L 0) (cfgConst L 1)
  rwa [crossRatio_const, Real.log_exp] at h

/-- **THE WALL, second form.**  Every Birkhoff contraction factor obtainable
from an admissible diameter is at least `tanh (β L)`. -/
theorem birkhoff_bound_ge {β : ℝ} (L : ℕ) (D : ℝ)
    (hD : ∀ σ σ' τ τ' : Fin L → Fin 2,
      Real.log (crossRatio (spatialKernel β) σ σ' τ τ') ≤ D) :
    Real.tanh (β * L) ≤ Real.tanh (D / 4) := by
  apply tanh_le_tanh
  have := projDiameter_ge L D hD
  linarith

/-- **THE WALL, third form: the degeneration is exponential in the volume.**
`tanh (β L)` is a lower bound for every Birkhoff factor this route produces
(`birkhoff_bound_ge`), and it is itself within `2 exp (-2 β L)` of the trivial
bound `1`.  No claim is made that the lower bound is attained. -/
theorem birkhoff_bound_near_one (β : ℝ) (L : ℕ) :
    1 - Real.tanh (β * L) ≤ 2 * Real.exp (-(2 * (β * L))) :=
  one_sub_tanh_le (β * L)

/-- **AND THE BOUND IS NOT TIGHT.**  For the decoupled kernel O-3f computes the
subdominant ratio exactly: it is `tanh β`, at every `L`.  From `L = 1` on, the
Birkhoff factor `tanh (β L)` is no better, and for `L ≥ 2` with `β > 0` it is
strictly worse.  The degeneration above is therefore a property of the method,
not of the model. -/
theorem birkhoff_bound_not_tight {β : ℝ} (hβ : 0 < β) {L : ℕ} (hL : 2 ≤ L) :
    Real.tanh β < Real.tanh (β * L) := by
  rw [tanh_eq_one_sub, tanh_eq_one_sub]
  have hlt : (2:ℝ) * β < 2 * (β * L) := by
    have : (2:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL
    nlinarith
  have hexp : Real.exp (2 * β) < Real.exp (2 * (β * L)) := Real.exp_lt_exp.mpr hlt
  have h1 : (0:ℝ) < Real.exp (2 * β) + 1 := by positivity
  have h2 : (0:ℝ) < Real.exp (2 * (β * L)) + 1 := by positivity
  have hkey : 2 / (Real.exp (2 * (β * L)) + 1) < 2 / (Real.exp (2 * β) + 1) := by
    rw [div_lt_div_iff₀ h2 h1]
    linarith
  linarith

/-! ## §5  The blindness is TWO-SIDED, so the symmetrised kernel is covered -/

/-- **THE BLINDNESS IS TWO-SIDED.**  The projective cross-ratio is unchanged by
multiplying a kernel by a nowhere-zero function of the source *and* a
nowhere-zero function of the target: all four factors occur once above and once
below the bar.  This is strictly stronger than
`crossRatio_sourceWeighted`, and it is what covers the symmetrised convention. -/
theorem crossRatio_twoSided {α : Type*} (A : α → α → ℝ) (u v : α → ℝ)
    (hu : ∀ x, u x ≠ 0) (hv : ∀ x, v x ≠ 0) (σ σ' τ τ' : α) :
    crossRatio (fun x y => u x * A x y * v y) σ σ' τ τ'
      = crossRatio A σ σ' τ τ' := by
  unfold crossRatio
  rw [show u σ * A σ τ * v τ * (u σ' * A σ' τ' * v τ')
        = u σ * u σ' * (v τ * v τ') * (A σ τ * A σ' τ') by ring,
      show u σ * A σ τ' * v τ' * (u σ' * A σ' τ * v τ)
        = u σ * u σ' * (v τ * v τ') * (A σ τ' * A σ' τ) by ring]
  exact mul_div_mul_left _ _
    (mul_ne_zero (mul_ne_zero (hu σ) (hu σ')) (mul_ne_zero (hv τ) (hv τ')))

/-- The symmetrised coupled kernel, `w(σ)^{1/2} K(σ,τ) w(τ)^{1/2}` — the
convention usual in the physics literature, and the one a reader of O-3f asks
about. -/
noncomputable def symCoupledKernel (β γ : ℝ) (σ τ : Fin 2 → Fin 2) : ℝ :=
  Real.sqrt (spatialWeight γ σ) * spatialKernel β σ τ *
    Real.sqrt (spatialWeight γ τ)

/-- **The symmetrised kernel is invisible to the metric too.**  O-3f could only
record this as prose; here it is a theorem.  So the blindness is not an artifact
of carrying the spatial weight on the source. -/
theorem crossRatio_symCoupledKernel (β γ : ℝ) (σ σ' τ τ' : Fin 2 → Fin 2) :
    crossRatio (symCoupledKernel β γ) σ σ' τ τ'
      = crossRatio (spatialKernel β) σ σ' τ τ' := by
  have h : ∀ x : Fin 2 → Fin 2, Real.sqrt (spatialWeight γ x) ≠ 0 := fun x =>
    ne_of_gt (Real.sqrt_pos.mpr (spatialWeight_pos γ x))
  exact crossRatio_twoSided (spatialKernel β)
    (fun x => Real.sqrt (spatialWeight γ x))
    (fun x => Real.sqrt (spatialWeight γ x)) h h σ σ' τ τ'

end YangMills.OS
