/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.L1_GibbsMeasure.GibbsMeasure
import YangMills.L1_GibbsMeasure.CenterInvariance

/-!
# Polymer representation, step 1 — the high-temperature expansion

The bridge from the lattice Gibbs theory to the verified Kotecký–Preiss
machinery begins with the **Mayer/high-temperature expansion** of the
Boltzmann weight: writing `exp(-β·E_p) = 1 + f_p` per plaquette,

  `exp(-β·S(A)) = ∏_p (1 + f_p(A)) = ∑_{S ⊆ plaquettes} ∏_{p∈S} f_p(A)`,

so the partition function is a **polymer-gas sum over plaquette sets**
(`partitionFunction_eq_sum_plaquetteSets`), with per-plaquette activities
bounded by `e^{|β|·B} − 1` for bounded plaquette energy
(`abs_plaquetteWeight_le`) — small at small `β`, which is exactly the
smallness the KP criterion consumes downstream.

This is step 1 of the polymer representation
(`docs/DEPENDENCY-GRAPH.md` §4 item 4).  Step 2 (grouping plaquette sets
into connected polymers and matching `PolymerSystem`/`KPCriterion`) is the
next campaign.  No character theory (T4) is needed on this route.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills

open MeasureTheory GaugeConfig

attribute [local instance] FiniteLatticeGeometry.fintypeP

variable {d N : ℕ} {G : Type*} [Group G] [FiniteLatticeGeometry d N G]

/-- The **Mayer weight** of a plaquette: `f_p(A) = exp(-β·E(hol_p A)) − 1`.
These are the polymer-gas activities of the high-temperature expansion. -/
noncomputable def plaquetteWeight (pe : G → ℝ) (β : ℝ)
    (A : GaugeConfig d N G)
    (p : FiniteLatticeGeometry.P (d := d) (N := N) (G := G)) : ℝ :=
  Real.exp (-β * pe (plaquetteHolonomy A p)) - 1

/-- **The high-temperature expansion of the Boltzmann weight:**
`exp(-β·S(A)) = ∑_{S ⊆ plaquettes} ∏_{p∈S} f_p(A)`. -/
theorem boltzmann_eq_sum_plaquetteSets (pe : G → ℝ) (β : ℝ)
    (A : GaugeConfig d N G) :
    Real.exp (-β * wilsonAction pe A)
      = ∑ S ∈ (Finset.univ :
          Finset (FiniteLatticeGeometry.P (d := d) (N := N) (G := G))).powerset,
          ∏ p ∈ S, plaquetteWeight pe β A p := by
  classical
  unfold wilsonAction
  rw [show -β * (∑ p : FiniteLatticeGeometry.P (d := d) (N := N) (G := G),
      pe (plaquetteHolonomy A p))
      = ∑ p : FiniteLatticeGeometry.P (d := d) (N := N) (G := G),
        (-β * pe (plaquetteHolonomy A p)) from Finset.mul_sum _ _ _]
  rw [Real.exp_sum]
  have hfac : ∀ p ∈ (Finset.univ :
      Finset (FiniteLatticeGeometry.P (d := d) (N := N) (G := G))),
      Real.exp (-β * pe (plaquetteHolonomy A p))
        = plaquetteWeight pe β A p + 1 := by
    intro p _
    unfold plaquetteWeight
    ring
  rw [Finset.prod_congr rfl hfac, Finset.prod_add]
  exact Finset.sum_congr rfl fun t _ => by
    rw [Finset.prod_const_one, mul_one]

/-- **The partition function as a polymer-gas sum:** integrating the
high-temperature expansion termwise (under explicit integrability of each
finite product — automatic for bounded energies). -/
theorem partitionFunction_eq_sum_plaquetteSets [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ] (pe : G → ℝ) (β : ℝ)
    (hint : ∀ S ∈ (Finset.univ :
        Finset (FiniteLatticeGeometry.P (d := d) (N := N) (G := G))).powerset,
      Integrable (fun A : GaugeConfig d N G => ∏ p ∈ S, plaquetteWeight pe β A p)
        (gaugeMeasureFrom (d := d) (N := N) μ)) :
    partitionFunction (d := d) (N := N) μ pe β
      = ∑ S ∈ (Finset.univ :
          Finset (FiniteLatticeGeometry.P (d := d) (N := N) (G := G))).powerset,
          ∫ A, ∏ p ∈ S, plaquetteWeight pe β A p
            ∂(gaugeMeasureFrom (d := d) (N := N) μ) := by
  unfold partitionFunction
  rw [show (fun U : GaugeConfig d N G => Real.exp (-β * wilsonAction pe U))
      = fun U => ∑ S ∈ (Finset.univ :
          Finset (FiniteLatticeGeometry.P (d := d) (N := N) (G := G))).powerset,
          ∏ p ∈ S, plaquetteWeight pe β U p from
    funext fun U => boltzmann_eq_sum_plaquetteSets pe β U]
  exact MeasureTheory.integral_finset_sum _ hint

/-- `|e^t − 1| ≤ e^{|t|} − 1` (the two-sided exponential bound). -/
private lemma abs_exp_sub_one_le_exp_abs (t : ℝ) :
    |Real.exp t - 1| ≤ Real.exp |t| - 1 := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht, abs_of_nonneg
      (by linarith [Real.one_le_exp ht] : (0 : ℝ) ≤ Real.exp t - 1)]
  · rw [abs_of_neg ht, abs_of_nonpos
      (by linarith [Real.exp_lt_one_iff.mpr ht] : Real.exp t - 1 ≤ 0)]
    have h1 := Real.add_one_le_exp t
    have h2 := Real.add_one_le_exp (-t)
    linarith

/-- **Activity smallness:** for plaquette energy bounded by `B`, every Mayer
weight is bounded by `e^{|β|·B} − 1` — uniformly small at small coupling.
This is the seed of the KP smallness criterion for the plaquette polymer
gas. -/
theorem abs_plaquetteWeight_le (pe : G → ℝ) (β : ℝ)
    (A : GaugeConfig d N G)
    (p : FiniteLatticeGeometry.P (d := d) (N := N) (G := G))
    {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) :
    |plaquetteWeight pe β A p| ≤ Real.exp (|β| * B) - 1 := by
  unfold plaquetteWeight
  refine le_trans (abs_exp_sub_one_le_exp_abs _) ?_
  have h1 : |(-β) * pe (plaquetteHolonomy A p)| ≤ |β| * B := by
    rw [abs_mul, abs_neg]
    have hB : (0 : ℝ) ≤ B := le_trans (abs_nonneg _) (hpe 1)
    exact mul_le_mul_of_nonneg_left (hpe _) (abs_nonneg β)
  have h2 : Real.exp |(-β) * pe (plaquetteHolonomy A p)|
      ≤ Real.exp (|β| * B) := Real.exp_le_exp.mpr h1
  have h3 : -β * pe (plaquetteHolonomy A p)
      = (-β) * pe (plaquetteHolonomy A p) := by ring
  rw [h3]
  linarith

/-! ### Discharging the integrability hypothesis -/

section Integrability

variable {d N : ℕ} [NeZero d] [NeZero N] {G : Type*} [Group G] [MeasurableSpace G]

/-- Evaluation of a negatively-oriented edge is the inverse of its positive
partner. -/
lemma config_apply_neg (A : GaugeConfig d N G) (e : ConcreteEdge d N)
    (he : e.sign = false) :
    A e = (A { e with sign := true })⁻¹ := by
  have hmr := A.map_reverse e
  rw [finBoxGeometry_reverse] at hmr
  have h2 : A { e with sign := true } = (A e)⁻¹ := by
    simpa [he] using hmr
  rw [h2, inv_inv]

/-- **Edge evaluation is measurable** (inversion-measurable group). -/
lemma measurable_config_apply [MeasurableInv G] (e : ConcreteEdge d N) :
    Measurable (fun A : GaugeConfig d N G => A e) := by
  have hpos : ∀ (e' : ConcreteEdge d N), e'.sign = true →
      Measurable (fun A : GaugeConfig d N G => A e') := by
    intro e' he'
    have : (fun A : GaugeConfig d N G => A e')
        = (fun f : PosEdge d N → G => f ⟨e', he'⟩) ∘
          (gaugeConfigMEquiv (d := d) (N := N) (G := G)).symm := by
      funext A
      rfl
    rw [this]
    exact (measurable_pi_apply _).comp
      (gaugeConfigMEquiv (d := d) (N := N) (G := G)).symm.measurable
  by_cases he : e.sign = true
  · exact hpos e he
  · have he' : e.sign = false := by
      rwa [Bool.not_eq_true] at he
    have hrw : (fun A : GaugeConfig d N G => A e)
        = fun A => (A { e with sign := true })⁻¹ := by
      funext A
      exact config_apply_neg A e he'
    rw [hrw]
    exact (hpos _ rfl).inv

/-- **Plaquette holonomies are measurable.** -/
lemma measurable_plaquetteHolonomy [MeasurableMul₂ G] [MeasurableInv G]
    (p : FiniteLatticeGeometry.P (d := d) (N := N) (G := G)) :
    Measurable (fun A : GaugeConfig d N G => plaquetteHolonomy A p) := by
  unfold plaquetteHolonomy
  exact (((measurable_config_apply _).mul (measurable_config_apply _)).mul
    (measurable_config_apply _)).mul (measurable_config_apply _)

/-- **Mayer-weight products are integrable** for bounded measurable
plaquette energies — the integrability hypothesis of the polymer-gas
formula, discharged. -/
lemma integrable_prod_plaquetteWeight [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ] {pe : G → ℝ}
    (hpe_meas : Measurable pe) {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (S : Finset (FiniteLatticeGeometry.P (d := d) (N := N) (G := G))) :
    Integrable (fun A : GaugeConfig d N G => ∏ p ∈ S, plaquetteWeight pe β A p)
      (gaugeMeasureFrom (d := d) (N := N) μ) := by
  have hmeas : Measurable
      (fun A : GaugeConfig d N G => ∏ p ∈ S, plaquetteWeight pe β A p) := by
    refine Finset.measurable_prod _ fun p _ => ?_
    unfold plaquetteWeight
    exact (Real.measurable_exp.comp
      ((hpe_meas.comp (measurable_plaquetteHolonomy p)).const_mul (-β))).sub
      measurable_const
  refine (MeasureTheory.integrable_const
    ((Real.exp (|β| * B) - 1) ^ S.card)).mono' hmeas.aestronglyMeasurable ?_
  refine MeasureTheory.ae_of_all _ fun A => ?_
  rw [Real.norm_eq_abs, Finset.abs_prod]
  calc ∏ p ∈ S, |plaquetteWeight pe β A p|
      ≤ ∏ _p ∈ S, (Real.exp (|β| * B) - 1) :=
        Finset.prod_le_prod (fun p _ => abs_nonneg _)
          (fun p _ => abs_plaquetteWeight_le pe β A p hpe)
    _ = (Real.exp (|β| * B) - 1) ^ S.card := by
        rw [Finset.prod_const]

/-- **The polymer-gas formula, unconditional for bounded measurable
energies:** the integrability hypothesis of
`partitionFunction_eq_sum_plaquetteSets` is discharged. -/
theorem partitionFunction_eq_sum_plaquetteSets'
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ] {pe : G → ℝ}
    (hpe_meas : Measurable pe) {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ) :
    partitionFunction (d := d) (N := N) μ pe β
      = ∑ S ∈ (Finset.univ :
          Finset (FiniteLatticeGeometry.P (d := d) (N := N) (G := G))).powerset,
          ∫ A, ∏ p ∈ S, plaquetteWeight pe β A p
            ∂(gaugeMeasureFrom (d := d) (N := N) μ) :=
  partitionFunction_eq_sum_plaquetteSets μ pe β
    (fun S _ => integrable_prod_plaquetteWeight μ hpe_meas hpe β S)

end Integrability

end YangMills
