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

set_option maxHeartbeats 3200000 in
open Classical in
/-- **THE TWO-PLAQUETTE CORRELATOR BOUND (T4, without Peter–Weyl):**
for a bounded measurable observable `f` of the plaquette holonomy, the
unnormalized connected two-plaquette correlator decays exponentially
in the touching-distance — with constants explicit in
`d, β, B, s, t, ε` and never the volume.  This is the
`kp_cluster_decay`-shaped statement of `PETER_WEYL_ROADMAP.md` (its
Layer-4 endpoint), reached through the weighted-Mayer machinery at
singleton supports with the `s`-scaled encoding `O = 1 + s·f` —
bypassing Peter–Weyl, Schur orthogonality, and the character
expansion entirely. -/
theorem two_plaquette_correlator_bound
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B : ℝ} (hpe : ∀ g', |pe g'| ≤ B) (β : ℝ)
    {f : G → ℝ} (hfm : Measurable f) (hf : ∀ x, |f x| ≤ 1)
    {s : ℝ} (hs0 : 0 < s)
    (t ε : ℝ) (ht0 : 0 ≤ t) (hε0 : 0 ≤ ε)
    (hr : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      (((Real.exp (|β| * B) - 1) + s +
        (Real.exp (|β| * B) - 1) * s) * Real.exp (t + ε + 1)) < 1)
    (hsmall : ((16 * d : ℕ) : ℝ) *
      ((((Real.exp (|β| * B) - 1) + s +
        (Real.exp (|β| * B) - 1) * s) * Real.exp (t + ε + 1)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          (((Real.exp (|β| * B) - 1) + s +
            (Real.exp (|β| * B) - 1) * s) *
            Real.exp (t + ε + 1)))) ≤ t)
    (p q : ConcretePlaquette d N) (k : ℕ) (hpq : p ≠ q)
    (hdist : 2 * k ≤ (touchGraph d N).dist p q)
    (hone : 4 * Real.exp (-(ε * k)) *
      ((((Real.exp (|β| * B) - 1) + s +
        (Real.exp (|β| * B) - 1) * s) * Real.exp (t + ε + 1)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          (((Real.exp (|β| * B) - 1) + s +
            (Real.exp (|β| * B) - 1) * s) *
            Real.exp (t + ε + 1)))) ≤ 1) :
    |(∫ A, f (plaquetteHolonomy A p) * f (plaquetteHolonomy A q) *
        Real.exp (-β * wilsonAction pe A)
        ∂(gaugeMeasureFrom (d := d) (N := N) μ)) *
      partitionFunction (d := d) (N := N) μ pe β
      - (∫ A, f (plaquetteHolonomy A p) *
          Real.exp (-β * wilsonAction pe A)
          ∂(gaugeMeasureFrom (d := d) (N := N) μ)) *
        (∫ A, f (plaquetteHolonomy A q) *
          Real.exp (-β * wilsonAction pe A)
          ∂(gaugeMeasureFrom (d := d) (N := N) μ))|
    ≤ (8 * ((((Real.exp (|β| * B) - 1) + s +
        (Real.exp (|β| * B) - 1) * s) * Real.exp (t + ε + 1)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          (((Real.exp (|β| * B) - 1) + s +
            (Real.exp (|β| * B) - 1) * s) *
            Real.exp (t + ε + 1)))) *
        (1 + s) ^ 2 *
        (partitionFunction (d := d) (N := N) μ pe β) ^ 2 *
        Real.exp (-(ε * k))) / s ^ 2 := by
  classical
  -- the Gibbs-form bound at singleton supports
  have hST : Disjoint ({p} : Finset (ConcretePlaquette d N)) {q} :=
    Finset.disjoint_singleton.mpr hpq
  have hdist' : ∀ p' ∈ ({p} : Finset (ConcretePlaquette d N)),
      ∀ q' ∈ ({q} : Finset (ConcretePlaquette d N)),
      2 * k ≤ (touchGraph d N).dist p' q' := by
    intro p' hp' q' hq'
    rw [Finset.mem_singleton] at hp' hq'
    subst hp'
    subst hq'
    exact hdist
  have hone' : 4 * (((({p} : Finset (ConcretePlaquette d N)).card : ℝ)) *
      ((({q} : Finset (ConcretePlaquette d N)).card : ℝ))) *
      Real.exp (-(ε * k)) *
      ((((Real.exp (|β| * B) - 1) + s +
        (Real.exp (|β| * B) - 1) * s) * Real.exp (t + ε + 1)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          (((Real.exp (|β| * B) - 1) + s +
            (Real.exp (|β| * B) - 1) * s) *
            Real.exp (t + ε + 1)))) ≤ 1 := by
    simpa using hone
  have h := gibbs_truncated_correlation_bound μ hpe_meas hpe β
    (isLocalWeight_obs f s) (measurable_obs hfm s)
    (le_of_lt hs0)
    (fun A p' => by
      have := abs_obs_le hf s A p'
      rwa [abs_of_pos hs0, mul_one] at this)
    t ε ht0 hε0 hr hsmall ({p} : Finset (ConcretePlaquette d N))
    ({q} : Finset (ConcretePlaquette d N)) k hST hdist' hone'
  -- collapse the singleton products
  rw [show (∫ A, (∏ p' ∈ ({p} : Finset (ConcretePlaquette d N)),
        (1 + (fun A p' => s * f (plaquetteHolonomy A p')) A p')) *
        (∏ p' ∈ ({q} : Finset (ConcretePlaquette d N)),
          (1 + (fun A p' => s * f (plaquetteHolonomy A p')) A p')) *
        Real.exp (-β * wilsonAction pe A)
        ∂(gaugeMeasureFrom (d := d) (N := N) μ))
      = ∫ A, (1 + s * f (plaquetteHolonomy A p)) *
          (1 + s * f (plaquetteHolonomy A q)) *
          Real.exp (-β * wilsonAction pe A)
          ∂(gaugeMeasureFrom (d := d) (N := N) μ) from by
        congr 1
        funext A
        simp only [Finset.prod_singleton]] at h
  rw [show (∫ A, (∏ p' ∈ ({p} : Finset (ConcretePlaquette d N)),
        (1 + (fun A p' => s * f (plaquetteHolonomy A p')) A p')) *
        Real.exp (-β * wilsonAction pe A)
        ∂(gaugeMeasureFrom (d := d) (N := N) μ))
      = ∫ A, (1 + s * f (plaquetteHolonomy A p)) *
          Real.exp (-β * wilsonAction pe A)
          ∂(gaugeMeasureFrom (d := d) (N := N) μ) from by
        congr 1
        funext A
        simp only [Finset.prod_singleton]] at h
  rw [show (∫ A, (∏ p' ∈ ({q} : Finset (ConcretePlaquette d N)),
        (1 + (fun A p' => s * f (plaquetteHolonomy A p')) A p')) *
        Real.exp (-β * wilsonAction pe A)
        ∂(gaugeMeasureFrom (d := d) (N := N) μ))
      = ∫ A, (1 + s * f (plaquetteHolonomy A q)) *
          Real.exp (-β * wilsonAction pe A)
          ∂(gaugeMeasureFrom (d := d) (N := N) μ) from by
        congr 1
        funext A
        simp only [Finset.prod_singleton]] at h
  -- integrability of the pieces
  have hI0 := integrable_boltzmann (d := d) (N := N) μ hpe_meas hpe β
  have hmp : Measurable (fun A : GaugeConfig d N G =>
      f (plaquetteHolonomy A p)) :=
    hfm.comp (measurable_plaquetteHolonomy p)
  have hmq : Measurable (fun A : GaugeConfig d N G =>
      f (plaquetteHolonomy A q)) :=
    hfm.comp (measurable_plaquetteHolonomy q)
  have hIp : MeasureTheory.Integrable (fun A : GaugeConfig d N G =>
      f (plaquetteHolonomy A p) * Real.exp (-β * wilsonAction pe A))
      (gaugeMeasureFrom (d := d) (N := N) μ) :=
    hI0.bdd_mul hmp.aestronglyMeasurable
      (MeasureTheory.ae_of_all _ fun A => by
        rw [Real.norm_eq_abs]; exact hf _)
  have hIq : MeasureTheory.Integrable (fun A : GaugeConfig d N G =>
      f (plaquetteHolonomy A q) * Real.exp (-β * wilsonAction pe A))
      (gaugeMeasureFrom (d := d) (N := N) μ) :=
    hI0.bdd_mul hmq.aestronglyMeasurable
      (MeasureTheory.ae_of_all _ fun A => by
        rw [Real.norm_eq_abs]; exact hf _)
  have hIpq : MeasureTheory.Integrable (fun A : GaugeConfig d N G =>
      f (plaquetteHolonomy A p) * f (plaquetteHolonomy A q) *
        Real.exp (-β * wilsonAction pe A))
      (gaugeMeasureFrom (d := d) (N := N) μ) :=
    hI0.bdd_mul (hmp.mul hmq).aestronglyMeasurable
      (MeasureTheory.ae_of_all _ fun A => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_one₀ (hf _) (abs_nonneg _) (hf _))
  -- the bilinear expansions
  have he12 : (∫ A, (1 + s * f (plaquetteHolonomy A p)) *
        (1 + s * f (plaquetteHolonomy A q)) *
        Real.exp (-β * wilsonAction pe A)
        ∂(gaugeMeasureFrom (d := d) (N := N) μ))
      = partitionFunction (d := d) (N := N) μ pe β
        + s * (∫ A, f (plaquetteHolonomy A p) *
            Real.exp (-β * wilsonAction pe A)
            ∂(gaugeMeasureFrom (d := d) (N := N) μ))
        + s * (∫ A, f (plaquetteHolonomy A q) *
            Real.exp (-β * wilsonAction pe A)
            ∂(gaugeMeasureFrom (d := d) (N := N) μ))
        + s * s * (∫ A, f (plaquetteHolonomy A p) *
            f (plaquetteHolonomy A q) *
            Real.exp (-β * wilsonAction pe A)
            ∂(gaugeMeasureFrom (d := d) (N := N) μ)) := by
    have hb1 : MeasureTheory.Integrable (fun A : GaugeConfig d N G =>
        s * (f (plaquetteHolonomy A q) *
          Real.exp (-β * wilsonAction pe A))
        + s * s * (f (plaquetteHolonomy A p) *
            f (plaquetteHolonomy A q) *
            Real.exp (-β * wilsonAction pe A)))
        (gaugeMeasureFrom (d := d) (N := N) μ) :=
      (hIq.const_mul s).add (hIpq.const_mul (s * s))
    have hb2 : MeasureTheory.Integrable (fun A : GaugeConfig d N G =>
        s * (f (plaquetteHolonomy A p) *
          Real.exp (-β * wilsonAction pe A))
        + (s * (f (plaquetteHolonomy A q) *
            Real.exp (-β * wilsonAction pe A))
        + s * s * (f (plaquetteHolonomy A p) *
            f (plaquetteHolonomy A q) *
            Real.exp (-β * wilsonAction pe A))))
        (gaugeMeasureFrom (d := d) (N := N) μ) :=
      (hIp.const_mul s).add hb1
    have e0 : (∫ A, (1 + s * f (plaquetteHolonomy A p)) *
          (1 + s * f (plaquetteHolonomy A q)) *
          Real.exp (-β * wilsonAction pe A)
          ∂(gaugeMeasureFrom (d := d) (N := N) μ))
        = ∫ A, (Real.exp (-β * wilsonAction pe A)
            + (s * (f (plaquetteHolonomy A p) *
                Real.exp (-β * wilsonAction pe A))
            + (s * (f (plaquetteHolonomy A q) *
                Real.exp (-β * wilsonAction pe A))
            + s * s * (f (plaquetteHolonomy A p) *
                f (plaquetteHolonomy A q) *
                Real.exp (-β * wilsonAction pe A)))))
            ∂(gaugeMeasureFrom (d := d) (N := N) μ) := by
      congr 1
      funext A
      ring
    have eA : (∫ A, (Real.exp (-β * wilsonAction pe A)
          + (s * (f (plaquetteHolonomy A p) *
              Real.exp (-β * wilsonAction pe A))
          + (s * (f (plaquetteHolonomy A q) *
              Real.exp (-β * wilsonAction pe A))
          + s * s * (f (plaquetteHolonomy A p) *
              f (plaquetteHolonomy A q) *
              Real.exp (-β * wilsonAction pe A)))))
          ∂(gaugeMeasureFrom (d := d) (N := N) μ))
        = (∫ A, Real.exp (-β * wilsonAction pe A)
            ∂(gaugeMeasureFrom (d := d) (N := N) μ))
          + ∫ A, (s * (f (plaquetteHolonomy A p) *
              Real.exp (-β * wilsonAction pe A))
            + (s * (f (plaquetteHolonomy A q) *
                Real.exp (-β * wilsonAction pe A))
            + s * s * (f (plaquetteHolonomy A p) *
                f (plaquetteHolonomy A q) *
                Real.exp (-β * wilsonAction pe A))))
            ∂(gaugeMeasureFrom (d := d) (N := N) μ) :=
      MeasureTheory.integral_add hI0 hb2
    have eB : (∫ A, (s * (f (plaquetteHolonomy A p) *
            Real.exp (-β * wilsonAction pe A))
          + (s * (f (plaquetteHolonomy A q) *
              Real.exp (-β * wilsonAction pe A))
          + s * s * (f (plaquetteHolonomy A p) *
              f (plaquetteHolonomy A q) *
              Real.exp (-β * wilsonAction pe A))))
          ∂(gaugeMeasureFrom (d := d) (N := N) μ))
        = (∫ A, s * (f (plaquetteHolonomy A p) *
            Real.exp (-β * wilsonAction pe A))
            ∂(gaugeMeasureFrom (d := d) (N := N) μ))
          + ∫ A, (s * (f (plaquetteHolonomy A q) *
              Real.exp (-β * wilsonAction pe A))
            + s * s * (f (plaquetteHolonomy A p) *
                f (plaquetteHolonomy A q) *
                Real.exp (-β * wilsonAction pe A)))
            ∂(gaugeMeasureFrom (d := d) (N := N) μ) :=
      MeasureTheory.integral_add (hIp.const_mul s) hb1
    have eC : (∫ A, (s * (f (plaquetteHolonomy A q) *
            Real.exp (-β * wilsonAction pe A))
          + s * s * (f (plaquetteHolonomy A p) *
              f (plaquetteHolonomy A q) *
              Real.exp (-β * wilsonAction pe A)))
          ∂(gaugeMeasureFrom (d := d) (N := N) μ))
        = (∫ A, s * (f (plaquetteHolonomy A q) *
            Real.exp (-β * wilsonAction pe A))
            ∂(gaugeMeasureFrom (d := d) (N := N) μ))
          + ∫ A, s * s * (f (plaquetteHolonomy A p) *
              f (plaquetteHolonomy A q) *
              Real.exp (-β * wilsonAction pe A))
            ∂(gaugeMeasureFrom (d := d) (N := N) μ) :=
      MeasureTheory.integral_add (hIq.const_mul s)
        (hIpq.const_mul (s * s))
    have eD : (∫ A, s * (f (plaquetteHolonomy A p) *
          Real.exp (-β * wilsonAction pe A))
          ∂(gaugeMeasureFrom (d := d) (N := N) μ))
        = s * ∫ A, f (plaquetteHolonomy A p) *
            Real.exp (-β * wilsonAction pe A)
            ∂(gaugeMeasureFrom (d := d) (N := N) μ) :=
      MeasureTheory.integral_const_mul _ _
    have eE : (∫ A, s * (f (plaquetteHolonomy A q) *
          Real.exp (-β * wilsonAction pe A))
          ∂(gaugeMeasureFrom (d := d) (N := N) μ))
        = s * ∫ A, f (plaquetteHolonomy A q) *
            Real.exp (-β * wilsonAction pe A)
            ∂(gaugeMeasureFrom (d := d) (N := N) μ) :=
      MeasureTheory.integral_const_mul _ _
    have eF : (∫ A, s * s * (f (plaquetteHolonomy A p) *
          f (plaquetteHolonomy A q) *
          Real.exp (-β * wilsonAction pe A))
          ∂(gaugeMeasureFrom (d := d) (N := N) μ))
        = s * s * ∫ A, f (plaquetteHolonomy A p) *
            f (plaquetteHolonomy A q) *
            Real.exp (-β * wilsonAction pe A)
            ∂(gaugeMeasureFrom (d := d) (N := N) μ) :=
      MeasureTheory.integral_const_mul _ _
    rw [e0, eA, eB, eC, eD, eE, eF]
    unfold partitionFunction
    ring
  have hexp1 : ∀ (r : ConcretePlaquette d N),
      (∫ A, (1 + s * f (plaquetteHolonomy A r)) *
        Real.exp (-β * wilsonAction pe A)
        ∂(gaugeMeasureFrom (d := d) (N := N) μ))
      = partitionFunction (d := d) (N := N) μ pe β
        + s * (∫ A, f (plaquetteHolonomy A r) *
            Real.exp (-β * wilsonAction pe A)
            ∂(gaugeMeasureFrom (d := d) (N := N) μ)) := by
    intro r
    have hIr : MeasureTheory.Integrable (fun A : GaugeConfig d N G =>
        f (plaquetteHolonomy A r) * Real.exp (-β * wilsonAction pe A))
        (gaugeMeasureFrom (d := d) (N := N) μ) :=
      hI0.bdd_mul ((hfm.comp
        (measurable_plaquetteHolonomy r)).aestronglyMeasurable)
        (MeasureTheory.ae_of_all _ fun A => by
        rw [Real.norm_eq_abs]; exact hf _)
    have e0 : (∫ A, (1 + s * f (plaquetteHolonomy A r)) *
          Real.exp (-β * wilsonAction pe A)
          ∂(gaugeMeasureFrom (d := d) (N := N) μ))
        = ∫ A, (Real.exp (-β * wilsonAction pe A)
            + s * (f (plaquetteHolonomy A r) *
                Real.exp (-β * wilsonAction pe A)))
            ∂(gaugeMeasureFrom (d := d) (N := N) μ) := by
      congr 1
      funext A
      ring
    have eA : (∫ A, (Real.exp (-β * wilsonAction pe A)
          + s * (f (plaquetteHolonomy A r) *
              Real.exp (-β * wilsonAction pe A)))
          ∂(gaugeMeasureFrom (d := d) (N := N) μ))
        = (∫ A, Real.exp (-β * wilsonAction pe A)
            ∂(gaugeMeasureFrom (d := d) (N := N) μ))
          + ∫ A, s * (f (plaquetteHolonomy A r) *
              Real.exp (-β * wilsonAction pe A))
            ∂(gaugeMeasureFrom (d := d) (N := N) μ) :=
      MeasureTheory.integral_add hI0 (hIr.const_mul s)
    have eD : (∫ A, s * (f (plaquetteHolonomy A r) *
          Real.exp (-β * wilsonAction pe A))
          ∂(gaugeMeasureFrom (d := d) (N := N) μ))
        = s * ∫ A, f (plaquetteHolonomy A r) *
            Real.exp (-β * wilsonAction pe A)
            ∂(gaugeMeasureFrom (d := d) (N := N) μ) :=
      MeasureTheory.integral_const_mul _ _
    rw [e0, eA, eD]
    unfold partitionFunction
    ring
  rw [he12, hexp1 p, hexp1 q] at h
  -- the s²-factorization of the difference
  set Z : ℝ := partitionFunction (d := d) (N := N) μ pe β with hZdef
  set I1 : ℝ := ∫ A, f (plaquetteHolonomy A p) *
    Real.exp (-β * wilsonAction pe A)
    ∂(gaugeMeasureFrom (d := d) (N := N) μ) with hI1def
  set I2 : ℝ := ∫ A, f (plaquetteHolonomy A q) *
    Real.exp (-β * wilsonAction pe A)
    ∂(gaugeMeasureFrom (d := d) (N := N) μ) with hI2def
  set I12 : ℝ := ∫ A, f (plaquetteHolonomy A p) *
    f (plaquetteHolonomy A q) *
    Real.exp (-β * wilsonAction pe A)
    ∂(gaugeMeasureFrom (d := d) (N := N) μ) with hI12def
  have hfac : (Z + s * I1 + s * I2 + s * s * I12) * Z
      - (Z + s * I1) * (Z + s * I2)
      = s * s * (I12 * Z - I1 * I2) := by ring
  rw [hfac, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < s * s)] at h
  -- bound the deformed partition factors by (1+s)·Z
  have hZ0 : (0 : ℝ) ≤ Z := by
    rw [hZdef]
    unfold partitionFunction
    exact MeasureTheory.integral_nonneg fun A => (Real.exp_pos _).le
  have hZfac : ∀ (r : ConcretePlaquette d N)
      (Ir : ℝ) (hIr : Ir = ∫ A, f (plaquetteHolonomy A r) *
        Real.exp (-β * wilsonAction pe A)
        ∂(gaugeMeasureFrom (d := d) (N := N) μ)),
      |Z + s * Ir| ≤ (1 + s) * Z := by
    intro r Ir hIr
    have hIr' : MeasureTheory.Integrable (fun A : GaugeConfig d N G =>
        f (plaquetteHolonomy A r) * Real.exp (-β * wilsonAction pe A))
        (gaugeMeasureFrom (d := d) (N := N) μ) :=
      hI0.bdd_mul ((hfm.comp
        (measurable_plaquetteHolonomy r)).aestronglyMeasurable)
        (MeasureTheory.ae_of_all _ fun A => by
        rw [Real.norm_eq_abs]; exact hf _)
    have hback : Z + s * Ir = ∫ A,
        (1 + s * f (plaquetteHolonomy A r)) *
        Real.exp (-β * wilsonAction pe A)
        ∂(gaugeMeasureFrom (d := d) (N := N) μ) := by
      rw [hIr, hexp1 r]
    rw [hback]
    refine le_trans (MeasureTheory.abs_integral_le_integral_abs) ?_
    have hptw : ∀ A : GaugeConfig d N G,
        |(1 + s * f (plaquetteHolonomy A r)) *
          Real.exp (-β * wilsonAction pe A)|
        ≤ (1 + s) * Real.exp (-β * wilsonAction pe A) := by
      intro A
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      calc |1 + s * f (plaquetteHolonomy A r)|
          ≤ |(1 : ℝ)| + |s * f (plaquetteHolonomy A r)| := abs_add_le _ _
        _ ≤ 1 + s := by
            have := abs_obs_le hf s A r
            rw [abs_of_pos hs0, mul_one] at this
            rw [abs_one]
            linarith
    calc ∫ A, |(1 + s * f (plaquetteHolonomy A r)) *
          Real.exp (-β * wilsonAction pe A)|
          ∂(gaugeMeasureFrom (d := d) (N := N) μ)
        ≤ ∫ A, (1 + s) * Real.exp (-β * wilsonAction pe A)
          ∂(gaugeMeasureFrom (d := d) (N := N) μ) := by
          refine MeasureTheory.integral_mono ?_ (hI0.const_mul _)
            hptw
          exact (MeasureTheory.Integrable.add hI0
            (hIr'.const_mul s)).abs.congr (by
              refine MeasureTheory.ae_of_all _ fun A => ?_
              show |Real.exp (-β * wilsonAction pe A) +
                  s * (f (plaquetteHolonomy A r) *
                    Real.exp (-β * wilsonAction pe A))|
                = |(1 + s * f (plaquetteHolonomy A r)) *
                    Real.exp (-β * wilsonAction pe A)|
              congr 1
              ring)
      _ = (1 + s) * Z := by
          rw [MeasureTheory.integral_const_mul, hZdef]
          rfl
  have hZ1 := hZfac p I1 hI1def
  have hZ2 := hZfac q I2 hI2def
  -- assemble
  refine (le_div_iff₀ (by positivity : (0 : ℝ) < s ^ 2)).mpr ?_
  calc |I12 * Z - I1 * I2| * s ^ 2
      = s * s * |I12 * Z - I1 * I2| := by ring
    _ ≤ 8 * (((({p} : Finset (ConcretePlaquette d N)).card : ℝ)) *
          ((({q} : Finset (ConcretePlaquette d N)).card : ℝ))) *
        ((((Real.exp (|β| * B) - 1) + s +
          (Real.exp (|β| * B) - 1) * s) * Real.exp (t + ε + 1)) /
          (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
            (((Real.exp (|β| * B) - 1) + s +
              (Real.exp (|β| * B) - 1) * s) *
              Real.exp (t + ε + 1)))) *
        |Z + s * I1| * |Z + s * I2| * Real.exp (-(ε * k)) := h
    _ ≤ 8 * (((({p} : Finset (ConcretePlaquette d N)).card : ℝ)) *
          ((({q} : Finset (ConcretePlaquette d N)).card : ℝ))) *
        ((((Real.exp (|β| * B) - 1) + s +
          (Real.exp (|β| * B) - 1) * s) * Real.exp (t + ε + 1)) /
          (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
            (((Real.exp (|β| * B) - 1) + s +
              (Real.exp (|β| * B) - 1) * s) *
              Real.exp (t + ε + 1)))) *
        ((1 + s) * Z) * ((1 + s) * Z) * Real.exp (-(ε * k)) := by
        have hM0 : (0 : ℝ) ≤ (((Real.exp (|β| * B) - 1) + s +
            (Real.exp (|β| * B) - 1) * s) * Real.exp (t + ε + 1)) /
            (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
              (((Real.exp (|β| * B) - 1) + s +
                (Real.exp (|β| * B) - 1) * s) *
                Real.exp (t + ε + 1))) := by
          have hδw0 : (0 : ℝ) ≤ Real.exp (|β| * B) - 1 := by
            have h1 : (1 : ℝ) ≤ Real.exp (|β| * B) := by
              rw [← Real.exp_zero]
              refine Real.exp_le_exp.mpr ?_
              have hB : (0 : ℝ) ≤ B := le_trans (abs_nonneg _) (hpe 1)
              positivity
            linarith
          have hden : (0 : ℝ) < 1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
              (((Real.exp (|β| * B) - 1) + s +
                (Real.exp (|β| * B) - 1) * s) *
                Real.exp (t + ε + 1)) := by linarith
          exact div_nonneg (by positivity) hden.le
        gcongr
    _ = 8 * ((((Real.exp (|β| * B) - 1) + s +
          (Real.exp (|β| * B) - 1) * s) * Real.exp (t + ε + 1)) /
          (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
            (((Real.exp (|β| * B) - 1) + s +
              (Real.exp (|β| * B) - 1) * s) *
              Real.exp (t + ε + 1)))) *
        (1 + s) ^ 2 * Z ^ 2 * Real.exp (-(ε * k)) := by
        simp only [Finset.card_singleton, Nat.cast_one]
        ring

end YangMills
