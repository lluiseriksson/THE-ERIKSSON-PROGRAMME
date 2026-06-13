/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.L1_GibbsMeasure.PolymerRepresentation
import YangMills.ClayCore.SchurPhysicalBridge

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

set_option maxHeartbeats 1600000 in
open Classical in
/-- **THE NORMALIZED TWO-PLAQUETTE COVARIANCE BOUND** — dividing by
`Z² > 0` makes the constant `Z`-FREE: the genuine Gibbs covariance of
two bounded local holonomy observables at touching-distance `≥ 2k`
satisfies

    |⟨f_p·f_q⟩ − ⟨f_p⟩·⟨f_q⟩| ≤ (8·M·(1+s)²/s²)·e^{−ε·k}

with the constant depending only on `d, β, B, s, t, ε` — independent
of the volume AND of the partition function.  This is exponential
clustering of the lattice gauge theory's two-point functions at small
coupling, machine-checked end to end with no Peter–Weyl input. -/
theorem two_plaquette_correlator_bound_normalized
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
        ∂(gaugeMeasureFrom (d := d) (N := N) μ)) /
      partitionFunction (d := d) (N := N) μ pe β
      - ((∫ A, f (plaquetteHolonomy A p) *
          Real.exp (-β * wilsonAction pe A)
          ∂(gaugeMeasureFrom (d := d) (N := N) μ)) /
        partitionFunction (d := d) (N := N) μ pe β) *
        ((∫ A, f (plaquetteHolonomy A q) *
          Real.exp (-β * wilsonAction pe A)
          ∂(gaugeMeasureFrom (d := d) (N := N) μ)) /
        partitionFunction (d := d) (N := N) μ pe β)|
    ≤ (8 * ((((Real.exp (|β| * B) - 1) + s +
        (Real.exp (|β| * B) - 1) * s) * Real.exp (t + ε + 1)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          (((Real.exp (|β| * B) - 1) + s +
            (Real.exp (|β| * B) - 1) * s) *
            Real.exp (t + ε + 1)))) *
        (1 + s) ^ 2 / s ^ 2) *
      Real.exp (-(ε * k)) := by
  classical
  have h := two_plaquette_correlator_bound μ hpe_meas hpe β hfm hf
    hs0 t ε ht0 hε0 hr hsmall p q k hpq hdist hone
  have hZpos : (0 : ℝ) < partitionFunction (d := d) (N := N) μ pe β :=
    partitionFunction_pos' μ hpe_meas hpe β
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
  set M : ℝ := (((Real.exp (|β| * B) - 1) + s +
      (Real.exp (|β| * B) - 1) * s) * Real.exp (t + ε + 1)) /
      (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
        (((Real.exp (|β| * B) - 1) + s +
          (Real.exp (|β| * B) - 1) * s) *
          Real.exp (t + ε + 1))) with hMdef
  have hkey : I12 / Z - (I1 / Z) * (I2 / Z)
      = (I12 * Z - I1 * I2) / Z ^ 2 := by
    field_simp <;> ring
  rw [hkey, abs_div, abs_of_pos (by positivity : (0 : ℝ) < Z ^ 2),
    div_le_iff₀ (by positivity : (0 : ℝ) < Z ^ 2)]
  refine le_trans h (le_of_eq ?_)
  field_simp <;> ring

set_option maxHeartbeats 800000 in
/-- **Non-vacuity of the clustering window (adversarial audit):** at
`t = ε = 1`, the three smallness hypotheses of
`two_plaquette_correlator_bound(_normalized)` are SIMULTANEOUSLY
satisfiable for every dimension — every `0 ≤ δ' ≤ δ₀(d)` works, with
`δ₀(d) > 0` explicit.  Since `δ' = (e^{|β|B}−1) + s + (e^{|β|B}−1)·s
→ 0` as `β, s → 0`, the `(β, s)`-window is nonempty: the clustering
theorems are not vacuous. -/
lemma clustering_window_nonempty (d : ℕ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ' : ℝ, 0 ≤ δ' → δ' ≤ δ₀ →
      ((16 * d + 1 : ℕ) : ℝ) ^ 2 * (δ' * Real.exp (1 + 1 + 1)) < 1 ∧
      ((16 * d : ℕ) : ℝ) * ((δ' * Real.exp (1 + 1 + 1)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          (δ' * Real.exp (1 + 1 + 1)))) ≤ 1 ∧
      ∀ k : ℕ, 4 * Real.exp (-(1 * (k : ℝ))) *
        ((δ' * Real.exp (1 + 1 + 1)) /
          (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
            (δ' * Real.exp (1 + 1 + 1)))) ≤ 1 := by
  set K : ℝ := ((16 * d + 1 : ℕ) : ℝ) with hKdef
  have hK1 : (1 : ℝ) ≤ K := by
    rw [hKdef]
    exact_mod_cast Nat.le_add_left 1 (16 * d)
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  refine ⟨((K ^ 2 + 64 * (d : ℝ) + 8) * Real.exp (1 + 1 + 1))⁻¹,
    by positivity, ?_⟩
  intro δ' hδ'0 hδ'le
  set x : ℝ := δ' * Real.exp (1 + 1 + 1) with hxdef
  have hx0 : (0 : ℝ) ≤ x := by positivity
  -- the master inequality: x·(K² + 64d + 8) ≤ 1
  have hxu : x * (K ^ 2 + 64 * (d : ℝ) + 8) ≤ 1 := by
    have h2 : ((K ^ 2 + 64 * (d : ℝ) + 8) * Real.exp (1 + 1 + 1))⁻¹ *
        Real.exp (1 + 1 + 1) = (K ^ 2 + 64 * (d : ℝ) + 8)⁻¹ := by
      rw [mul_inv]
      field_simp
    calc x * (K ^ 2 + 64 * (d : ℝ) + 8)
        ≤ (K ^ 2 + 64 * (d : ℝ) + 8)⁻¹ *
          (K ^ 2 + 64 * (d : ℝ) + 8) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [hxdef, ← h2]
          exact mul_le_mul_of_nonneg_right hδ'le (Real.exp_pos _).le
      _ = 1 := inv_mul_cancel₀ (by positivity)
  -- hr
  have hr : K ^ 2 * x < 1 := by
    rcases eq_or_lt_of_le hx0 with h0 | hpos
    · rw [← h0]
      norm_num
    · nlinarith
  have hD : (0 : ℝ) < 1 - K ^ 2 * x := by linarith
  have h16 : ((16 * d : ℕ) : ℝ) = 16 * (d : ℝ) := by push_cast; ring
  refine ⟨hr, ?_, ?_⟩
  · -- hsmall at t = 1
    rw [h16, ← mul_div_assoc, div_le_one hD]
    nlinarith
  · -- hone for every k
    intro k
    have hexp1 : Real.exp (-(1 * (k : ℝ))) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hM0 : (0 : ℝ) ≤ x / (1 - K ^ 2 * x) :=
      div_nonneg hx0 hD.le
    calc 4 * Real.exp (-(1 * (k : ℝ))) * (x / (1 - K ^ 2 * x))
        ≤ 4 * 1 * (x / (1 - K ^ 2 * x)) := by
          refine mul_le_mul_of_nonneg_right ?_ hM0
          exact mul_le_mul_of_nonneg_left hexp1 (by norm_num)
      _ = 4 * (x / (1 - K ^ 2 * x)) := by ring
      _ ≤ 1 := by
          rw [← mul_div_assoc, div_le_one hD]
          nlinarith

set_option maxHeartbeats 1600000 in
open Classical in
/-- **EXPONENTIAL CLUSTERING FOR THE GENUINE SU(N) WILSON THEORY:**
the normalized two-plaquette covariance bound instantiated at the
actual gauge group `SU(N_c)`, the actual Haar probability measure
`sunHaarProb`, and the actual Wilson plaquette energy `Re tr U`
(`fundamentalObservable`, bounded by `N_c`).  For any bounded
measurable observable of the plaquette holonomy, at touching-distance
`≥ 2k` and small coupling, the Gibbs covariance decays like
`e^{−ε·k}` with constants depending only on `d, N_c, β, s, t, ε` —
independent of the lattice volume and of the partition function. -/
theorem sun_two_plaquette_correlator_bound
    (N_c : ℕ) [NeZero N_c]
    {f : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ}
    (hfm : Measurable f) (hf : ∀ x, |f x| ≤ 1)
    {s : ℝ} (hs0 : 0 < s) (β : ℝ)
    (t ε : ℝ) (ht0 : 0 ≤ t) (hε0 : 0 ≤ ε)
    (hr : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      (((Real.exp (|β| * (N_c : ℝ)) - 1) + s +
        (Real.exp (|β| * (N_c : ℝ)) - 1) * s) *
        Real.exp (t + ε + 1)) < 1)
    (hsmall : ((16 * d : ℕ) : ℝ) *
      ((((Real.exp (|β| * (N_c : ℝ)) - 1) + s +
        (Real.exp (|β| * (N_c : ℝ)) - 1) * s) *
        Real.exp (t + ε + 1)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          (((Real.exp (|β| * (N_c : ℝ)) - 1) + s +
            (Real.exp (|β| * (N_c : ℝ)) - 1) * s) *
            Real.exp (t + ε + 1)))) ≤ t)
    (p q : ConcretePlaquette d N) (k : ℕ) (hpq : p ≠ q)
    (hdist : 2 * k ≤ (touchGraph d N).dist p q)
    (hone : 4 * Real.exp (-(ε * k)) *
      ((((Real.exp (|β| * (N_c : ℝ)) - 1) + s +
        (Real.exp (|β| * (N_c : ℝ)) - 1) * s) *
        Real.exp (t + ε + 1)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          (((Real.exp (|β| * (N_c : ℝ)) - 1) + s +
            (Real.exp (|β| * (N_c : ℝ)) - 1) * s) *
            Real.exp (t + ε + 1)))) ≤ 1) :
    |(∫ A, f (plaquetteHolonomy A p) * f (plaquetteHolonomy A q) *
        Real.exp (-β * wilsonAction (fundamentalObservable N_c) A)
        ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c))) /
      partitionFunction (d := d) (N := N) (sunHaarProb N_c)
        (fundamentalObservable N_c) β
      - ((∫ A, f (plaquetteHolonomy A p) *
          Real.exp (-β * wilsonAction (fundamentalObservable N_c) A)
          ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c))) /
        partitionFunction (d := d) (N := N) (sunHaarProb N_c)
          (fundamentalObservable N_c) β) *
        ((∫ A, f (plaquetteHolonomy A q) *
          Real.exp (-β * wilsonAction (fundamentalObservable N_c) A)
          ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c))) /
        partitionFunction (d := d) (N := N) (sunHaarProb N_c)
          (fundamentalObservable N_c) β)|
    ≤ (8 * ((((Real.exp (|β| * (N_c : ℝ)) - 1) + s +
        (Real.exp (|β| * (N_c : ℝ)) - 1) * s) *
        Real.exp (t + ε + 1)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          (((Real.exp (|β| * (N_c : ℝ)) - 1) + s +
            (Real.exp (|β| * (N_c : ℝ)) - 1) * s) *
            Real.exp (t + ε + 1)))) *
        (1 + s) ^ 2 / s ^ 2) *
      Real.exp (-(ε * k)) := by
  haveI hsc : SecondCountableTopology
      (Matrix (Fin N_c) (Fin N_c) ℂ) := by
    change SecondCountableTopology (Fin N_c → Fin N_c → ℂ)
    infer_instance
  haveI : SecondCountableTopology
      ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) :=
    TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  haveI : MeasurableMul₂
      ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) := by
    infer_instance
  haveI : MeasurableInv
      ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) := by
    infer_instance
  exact two_plaquette_correlator_bound_normalized (sunHaarProb N_c)
    ((Complex.continuous_re.comp (continuous_trace_sub N_c)).measurable)
    (fundamentalObservable_bounded N_c) β hfm hf hs0 t ε ht0 hε0
    hr hsmall p q k hpq hdist hone

set_option maxHeartbeats 800000 in
/-- **Non-vacuity of the SU(N) capstone:** for every dimension and
every `N_c` there is an EXPLICIT coupling window `0 < |β| ≤ β₀` and
scaling `s > 0` in which all hypotheses of
`sun_two_plaquette_correlator_bound` hold (at `t = ε = 1`, for every
separation `k`).  The genuine SU(N) clustering theorem has
substance. -/
lemma sun_clustering_window_nonempty (d N_c : ℕ) [NeZero N_c] :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∃ s : ℝ, 0 < s ∧ ∀ β : ℝ, |β| ≤ β₀ →
      (((16 * d + 1 : ℕ) : ℝ) ^ 2 *
        (((Real.exp (|β| * (N_c : ℝ)) - 1) + s +
          (Real.exp (|β| * (N_c : ℝ)) - 1) * s) *
          Real.exp (1 + 1 + 1)) < 1 ∧
      ((16 * d : ℕ) : ℝ) *
        ((((Real.exp (|β| * (N_c : ℝ)) - 1) + s +
          (Real.exp (|β| * (N_c : ℝ)) - 1) * s) *
          Real.exp (1 + 1 + 1)) /
          (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
            (((Real.exp (|β| * (N_c : ℝ)) - 1) + s +
              (Real.exp (|β| * (N_c : ℝ)) - 1) * s) *
              Real.exp (1 + 1 + 1)))) ≤ 1 ∧
      ∀ k : ℕ, 4 * Real.exp (-(1 * (k : ℝ))) *
        ((((Real.exp (|β| * (N_c : ℝ)) - 1) + s +
          (Real.exp (|β| * (N_c : ℝ)) - 1) * s) *
          Real.exp (1 + 1 + 1)) /
          (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
            (((Real.exp (|β| * (N_c : ℝ)) - 1) + s +
              (Real.exp (|β| * (N_c : ℝ)) - 1) * s) *
              Real.exp (1 + 1 + 1)))) ≤ 1) := by
  classical
  obtain ⟨δ₀, hδ₀pos, hwin⟩ := clustering_window_nonempty d
  set δ₁ : ℝ := min δ₀ 1 with hδ₁def
  have hδ₁pos : 0 < δ₁ := lt_min hδ₀pos one_pos
  have hδ₁le1 : δ₁ ≤ 1 := min_le_right _ _
  have hδ₁leδ₀ : δ₁ ≤ δ₀ := min_le_left _ _
  have hNc : (0 : ℝ) < (N_c : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N_c)
  refine ⟨Real.log (1 + δ₁ / 4) / (N_c : ℝ), ?_, δ₁ / 4,
    by positivity, ?_⟩
  · refine div_pos (Real.log_pos ?_) hNc
    linarith
  intro β hβ
  -- the Wilson bound in the window
  have hδw : Real.exp (|β| * (N_c : ℝ)) - 1 ≤ δ₁ / 4 := by
    have h1 : |β| * (N_c : ℝ) ≤ Real.log (1 + δ₁ / 4) := by
      have h2 := mul_le_mul_of_nonneg_right hβ hNc.le
      rwa [div_mul_cancel₀ _ hNc.ne'] at h2
    have h3 : Real.exp (|β| * (N_c : ℝ)) ≤ 1 + δ₁ / 4 := by
      calc Real.exp (|β| * (N_c : ℝ))
          ≤ Real.exp (Real.log (1 + δ₁ / 4)) := Real.exp_le_exp.mpr h1
        _ = 1 + δ₁ / 4 := Real.exp_log (by linarith)
    linarith
  have hδw0 : (0 : ℝ) ≤ Real.exp (|β| * (N_c : ℝ)) - 1 := by
    have : (1 : ℝ) ≤ Real.exp (|β| * (N_c : ℝ)) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by positivity)
    linarith
  -- the combined deformation bound lands in the δ₀-window
  have hδ' : (Real.exp (|β| * (N_c : ℝ)) - 1) + δ₁ / 4 +
      (Real.exp (|β| * (N_c : ℝ)) - 1) * (δ₁ / 4) ≤ δ₀ := by
    have hsq : δ₁ * δ₁ ≤ δ₁ := by nlinarith
    have hmul : (Real.exp (|β| * (N_c : ℝ)) - 1) * (δ₁ / 4)
        ≤ (δ₁ / 4) * (δ₁ / 4) :=
      mul_le_mul_of_nonneg_right hδw (by positivity)
    nlinarith
  have hδ'0 : (0 : ℝ) ≤ (Real.exp (|β| * (N_c : ℝ)) - 1) + δ₁ / 4 +
      (Real.exp (|β| * (N_c : ℝ)) - 1) * (δ₁ / 4) := by positivity
  exact hwin _ hδ'0 hδ'

open Classical in
/-- **UNCONDITIONAL FIXED-LATTICE EXPONENTIAL CLUSTERING FOR SU(N)
WILSON THEORY.**  Assembling `sun_two_plaquette_correlator_bound` with
the non-empty window `sun_clustering_window_nonempty` (at `t = ε = 1`,
separation `k = ⌊dist/2⌋`): for every dimension `d` and rank `N_c`
there is an EXPLICIT coupling window `|β| ≤ β₀` (`β₀ > 0`) in which the
connected (truncated) two-plaquette correlator of the genuine SU(N_c)
Wilson Gibbs measure decays exponentially in the plaquette-graph
distance,

  `|⟨f_p f_q⟩ − ⟨f_p⟩⟨f_q⟩| ≤ C · exp(−(1/2)·dist(p,q))`,

for EVERY bounded measurable plaquette observable `f` (`|f| ≤ 1`) and
EVERY pair of distinct plaquettes, with `C` depending only on
`d, N_c, β`.  This carries **NO** hypothesis — it is the fixed-lattice
mass-gap (exponential-clustering) statement, unconditional, with a
certified non-empty coupling window; the §6.3 Balaban single-scale
input is needed only for the *continuum* (lattice-spacing → 0) limit,
not for this fixed-lattice result. -/
theorem sun_lattice_exponential_clustering (N_c : ℕ) [NeZero N_c] :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, |β| ≤ β₀ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ),
        Measurable f → (∀ x, |f x| ≤ 1) →
      ∀ p q : ConcretePlaquette d N, p ≠ q →
      |(∫ A, f (plaquetteHolonomy A p) * f (plaquetteHolonomy A q) *
          Real.exp (-β * wilsonAction (fundamentalObservable N_c) A)
          ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c))) /
        partitionFunction (d := d) (N := N) (sunHaarProb N_c)
          (fundamentalObservable N_c) β
        - ((∫ A, f (plaquetteHolonomy A p) *
            Real.exp (-β * wilsonAction (fundamentalObservable N_c) A)
            ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c))) /
          partitionFunction (d := d) (N := N) (sunHaarProb N_c)
            (fundamentalObservable N_c) β) *
          ((∫ A, f (plaquetteHolonomy A q) *
            Real.exp (-β * wilsonAction (fundamentalObservable N_c) A)
            ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c))) /
          partitionFunction (d := d) (N := N) (sunHaarProb N_c)
            (fundamentalObservable N_c) β)|
        ≤ C * Real.exp (-((1 : ℝ)/2 * ((touchGraph d N).dist p q : ℝ))) := by
  classical
  obtain ⟨β₀, hβ₀, s, hs, hwin⟩ := sun_clustering_window_nonempty d N_c
  refine ⟨β₀, hβ₀, fun β hβ => ?_⟩
  obtain ⟨hr, hsmall, hone⟩ := hwin β hβ
  -- nonnegativity of the source's amplitude bracket (raw form, t = ε = 1)
  have he1 : (1 : ℝ) ≤ Real.exp (|β| * (N_c : ℝ)) := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by positivity)
  have he10 : (0 : ℝ) ≤ Real.exp (|β| * (N_c : ℝ)) - 1 := by linarith
  have hBR0 : (0 : ℝ) ≤ ((Real.exp (|β| * (N_c : ℝ)) - 1) + s +
      (Real.exp (|β| * (N_c : ℝ)) - 1) * s) * Real.exp (1 + 1 + 1) :=
    mul_nonneg (by nlinarith [he10, hs.le, mul_nonneg he10 hs.le])
      (Real.exp_pos _).le
  have hden : (0 : ℝ) < 1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      (((Real.exp (|β| * (N_c : ℝ)) - 1) + s +
        (Real.exp (|β| * (N_c : ℝ)) - 1) * s) * Real.exp (1 + 1 + 1)) := by
    linarith [hr]
  -- the amplitude `that ≥ 0`
  have hthat0 : (0 : ℝ) ≤ 8 * ((((Real.exp (|β| * (N_c : ℝ)) - 1) + s +
        (Real.exp (|β| * (N_c : ℝ)) - 1) * s) * Real.exp (1 + 1 + 1)) /
      (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
        (((Real.exp (|β| * (N_c : ℝ)) - 1) + s +
          (Real.exp (|β| * (N_c : ℝ)) - 1) * s) * Real.exp (1 + 1 + 1)))) *
      (1 + s) ^ 2 / s ^ 2 :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (div_nonneg hBR0 hden.le)) (sq_nonneg _)) (sq_nonneg _)
  refine ⟨(8 * ((((Real.exp (|β| * (N_c : ℝ)) - 1) + s +
        (Real.exp (|β| * (N_c : ℝ)) - 1) * s) * Real.exp (1 + 1 + 1)) /
      (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
        (((Real.exp (|β| * (N_c : ℝ)) - 1) + s +
          (Real.exp (|β| * (N_c : ℝ)) - 1) * s) * Real.exp (1 + 1 + 1)))) *
      (1 + s) ^ 2 / s ^ 2) * Real.exp ((1 : ℝ) / 2),
    mul_nonneg hthat0 (Real.exp_pos _).le, fun f hfm hf p q hpq => ?_⟩
  set D : ℕ := (touchGraph d N).dist p q with hDdef
  set k : ℕ := D / 2 with hkdef
  have hdist : 2 * k ≤ D := by omega
  have hbd := sun_two_plaquette_correlator_bound N_c hfm hf hs β 1 1
    (by norm_num) (by norm_num) hr hsmall p q k hpq hdist (hone k)
  refine le_trans hbd ?_
  -- fold the (identical) source amplitude on both sides
  set RAW : ℝ := 8 * ((((Real.exp (|β| * (N_c : ℝ)) - 1) + s +
        (Real.exp (|β| * (N_c : ℝ)) - 1) * s) * Real.exp (1 + 1 + 1)) /
      (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
        (((Real.exp (|β| * (N_c : ℝ)) - 1) + s +
          (Real.exp (|β| * (N_c : ℝ)) - 1) * s) * Real.exp (1 + 1 + 1)))) *
      (1 + s) ^ 2 / s ^ 2 with hRAWdef
  have hRAW0 : 0 ≤ RAW := by rw [hRAWdef]; exact hthat0
  have hkge : (D : ℝ) ≤ 2 * (k : ℝ) + 1 := by
    have : D ≤ 2 * k + 1 := by omega
    exact_mod_cast this
  have hexp : Real.exp (-(1 * (k : ℝ)))
      ≤ Real.exp ((1 : ℝ) / 2) * Real.exp (-((1 : ℝ) / 2 * (D : ℝ))) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hkge]
  calc RAW * Real.exp (-(1 * (k : ℝ)))
      ≤ RAW * (Real.exp ((1 : ℝ) / 2) *
          Real.exp (-((1 : ℝ) / 2 * (D : ℝ)))) :=
        mul_le_mul_of_nonneg_left hexp hRAW0
    _ = RAW * Real.exp ((1 : ℝ) / 2) *
          Real.exp (-((1 : ℝ) / 2 * (D : ℝ))) := by ring

end YangMills
