/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.L0_Lattice.GaugeConfigurations

/-!
# Centre scaling of the plaquette holonomy (algebraic core of LG6)

The Wilson **loop** observable is `tr(U₀·U₁·U₂·U₃)` — a trace of a *matrix product*, not
a scalar edge product, so the Fubini vanishing (`GaugeMarginal.integral_prod_edges_eq_zero`)
does **not** apply to it (`HORIZON.md` §3.3, LG6).  The correct tool is the **centre
eigenvalue argument**: scaling each edge holonomy by a central element `z` multiplies the
length-`L` loop by `z^L`.  For a plaquette (`L = 4`) this is `z⁴`.

This file proves that purely-algebraic core: left-multiplying each of the four factors of
`plaquetteHolonomy` by a central `z` scales the holonomy by `z⁴`.  It is the group-theoretic
ingredient that, combined with left-invariance of `gaugeMeasureFrom` under the diagonal
centre action (the remaining measure-theoretic plumbing) and a character with `z⁴ ≠ 1`,
yields the (conditional) selection of loop expectations — and makes precise why a plaquette
loop does *not* vanish unless `N ∣ 4`.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.GaugeConfig

open YangMills

/-- **One central factor step.**  For central `z`, `(z^k · S) · (z · x) = z^{k+1} · (S·x)`. -/
private theorem center_step {G : Type*} [Monoid G] {z : G} (hz : ∀ y : G, Commute z y)
    (S x : G) (k : ℕ) : (z ^ k * S) * (z * x) = z ^ (k + 1) * (S * x) := by
  rw [mul_assoc (z ^ k) S (z * x), ← mul_assoc S z x, ← (hz S).eq,
      mul_assoc z S x, ← mul_assoc (z ^ k) z (S * x), ← pow_succ]

/-- **Centre scaling of a 4-factor ordered product.**  If `z` is central, then
left-multiplying each of four factors by `z` scales the product by `z^4`. -/
theorem center_smul_prod_four {G : Type*} [Monoid G] {z a b c d : G}
    (hz : ∀ y : G, Commute z y) :
    (z * a) * (z * b) * (z * c) * (z * d) = z ^ 4 * (a * b * c * d) := by
  calc (z * a) * (z * b) * (z * c) * (z * d)
      = (z ^ 1 * a) * (z * b) * (z * c) * (z * d) := by rw [pow_one]
    _ = (z ^ (1 + 1) * (a * b)) * (z * c) * (z * d) := by rw [center_step hz a b 1]
    _ = (z ^ (1 + 1 + 1) * (a * b * c)) * (z * d) := by rw [center_step hz (a * b) c (1 + 1)]
    _ = z ^ (1 + 1 + 1 + 1) * (a * b * c * d) := by
          rw [center_step hz (a * b * c) d (1 + 1 + 1)]
    _ = z ^ 4 * (a * b * c * d) := by norm_num

variable {d N : ℕ} {G : Type*} [Group G] [FiniteLatticeGeometry d N G]

/-- **Plaquette holonomy under a central edge rescaling scales by `z⁴`.**  If each edge
holonomy is left-multiplied by a central `z` (the diagonal centre action `A ↦ (e ↦ z·A e)`),
the plaquette holonomy is multiplied by `z⁴`.  This is the centre-eigenvalue identity at
the heart of the Wilson-loop selection rule (length 4 ⇒ exponent 4). -/
theorem plaquetteHolonomy_center_smul {z : G} (hz : ∀ y : G, Commute z y)
    (A : GaugeConfig d N G) (p : FiniteLatticeGeometry.P (d := d) (N := N) (G := G))
    (Az : GaugeConfig d N G) (hAz : ∀ e, Az e = z * A e) :
    plaquetteHolonomy Az p = z ^ 4 * plaquetteHolonomy A p := by
  simp only [plaquetteHolonomy, hAz]
  exact center_smul_prod_four hz

end YangMills.GaugeConfig
