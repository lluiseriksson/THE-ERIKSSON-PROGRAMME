/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.L1_GibbsMeasure.PolymerRepresentation

/-!
# The two-plaquette correlator (T4 shortcut, opening bricks)

`docs/CLUSTER-CORRELATION-PLAN.md` §3: the two-plaquette
connected-correlator decay falls to
`gibbs_truncated_correlation_bound` at SINGLETON supports with the
`s`-scaled encoding `O_p = 1 + s·f(hol_p)` — no Peter–Weyl, no
character expansion.  This file provides the observable-weight family:

* `plaquetteHolonomy_congr` — the holonomy depends only on the
  plaquette's own (positive-edge) support, extracted from
  `plaquetteWeight_congr`;
* `isLocalWeight_obs` / `measurable_obs` / `abs_obs_le` — the family
  `g A p := s·f(hol_p A)` is a bounded measurable local weight family,
  ready for the weighted-gas machinery.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills

open MeasureTheory GaugeConfig

variable {d N : ℕ} [NeZero d] [NeZero N]
variable {G : Type*} [Group G] [MeasurableSpace G]

/-- **Locality of the plaquette holonomy:** it depends only on the
configuration's positive-edge coordinates in `plaquetteSupport p`
(extracted from the proof of `plaquetteWeight_congr`). -/
lemma plaquetteHolonomy_congr (p : ConcretePlaquette d N)
    {A A' : GaugeConfig d N G}
    (h : ∀ e ∈ plaquetteSupport p, configToPos A e = configToPos A' e) :
    plaquetteHolonomy A p = plaquetteHolonomy A' p := by
  unfold plaquetteHolonomy
  have h0 := config_eval_eq_of_pos A A' (p.edges 0)
    (h _ (by simp [plaquetteSupport]))
  have h1 := config_eval_eq_of_pos A A' (p.edges 1)
    (h _ (by simp [plaquetteSupport]))
  have h2 := config_eval_eq_of_pos A A' (p.edges 2)
    (h _ (by simp [plaquetteSupport]))
  have h3 := config_eval_eq_of_pos A A' (p.edges 3)
    (h _ (by simp [plaquetteSupport]))
  rw [show (FiniteLatticeGeometry.plaquetteEdge
      (d := d) (N := N) (G := G) p 0) = p.edges 0 from rfl,
    show (FiniteLatticeGeometry.plaquetteEdge
      (d := d) (N := N) (G := G) p 1) = p.edges 1 from rfl,
    show (FiniteLatticeGeometry.plaquetteEdge
      (d := d) (N := N) (G := G) p 2) = p.edges 2 from rfl,
    show (FiniteLatticeGeometry.plaquetteEdge
      (d := d) (N := N) (G := G) p 3) = p.edges 3 from rfl,
    h0, h1, h2, h3]

/-- The `s`-scaled holonomy-observable family is a local weight
family. -/
lemma isLocalWeight_obs (f : G → ℝ) (s : ℝ) :
    IsLocalWeight (d := d) (N := N) (G := G)
      (fun A p => s * f (plaquetteHolonomy A p)) := by
  intro p A A' h
  show s * f (plaquetteHolonomy A p) = s * f (plaquetteHolonomy A' p)
  rw [plaquetteHolonomy_congr p h]

/-- The `s`-scaled holonomy-observable family is measurable. -/
lemma measurable_obs [MeasurableMul₂ G] [MeasurableInv G]
    {f : G → ℝ} (hf : Measurable f) (s : ℝ)
    (p : ConcretePlaquette d N) :
    Measurable (fun A : GaugeConfig d N G =>
      s * f (plaquetteHolonomy A p)) :=
  (hf.comp (measurable_plaquetteHolonomy p)).const_mul s

/-- The `s`-scaled holonomy-observable family is uniformly bounded. -/
lemma abs_obs_le {f : G → ℝ} {c : ℝ} (hf : ∀ x, |f x| ≤ c) (s : ℝ)
    (A : GaugeConfig d N G) (p : ConcretePlaquette d N) :
    |s * f (plaquetteHolonomy A p)| ≤ |s| * c := by
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hf _) (abs_nonneg s)

end YangMills
