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

/-- **The Wilson action is measurable** (bounded measurable energy not even
needed — measurability of `pe` suffices). -/
lemma measurable_wilsonAction [MeasurableMul₂ G] [MeasurableInv G]
    {pe : G → ℝ} (hpe_meas : Measurable pe) :
    Measurable (fun A : GaugeConfig d N G => wilsonAction pe A) := by
  unfold wilsonAction
  exact Finset.measurable_sum _ fun p _ =>
    hpe_meas.comp (measurable_plaquetteHolonomy p)

/-- **The Boltzmann weight is integrable** for bounded measurable plaquette
energies — discharging the integrability hypothesis carried by
`partitionFunction_pos` and `gibbsMeasure_isProbability`. -/
lemma integrable_boltzmann [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ] {pe : G → ℝ}
    (hpe_meas : Measurable pe) {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ) :
    Integrable
      (fun A : GaugeConfig d N G => Real.exp (-β * wilsonAction pe A))
      (gaugeMeasureFrom (d := d) (N := N) μ) := by
  have hmeas : Measurable
      (fun A : GaugeConfig d N G => Real.exp (-β * wilsonAction pe A)) :=
    Real.measurable_exp.comp ((measurable_wilsonAction hpe_meas).const_mul (-β))
  refine (MeasureTheory.integrable_const
    (Real.exp (|β| * B *
      (Fintype.card (FiniteLatticeGeometry.P (d := d) (N := N) (G := G)))))).mono'
    hmeas.aestronglyMeasurable ?_
  refine MeasureTheory.ae_of_all _ fun A => ?_
  rw [Real.norm_eq_abs, Real.abs_exp]
  refine Real.exp_le_exp.mpr ?_
  have hS : |wilsonAction pe A|
      ≤ B * (Fintype.card (FiniteLatticeGeometry.P (d := d) (N := N) (G := G))) := by
    unfold wilsonAction
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    calc ∑ p : FiniteLatticeGeometry.P (d := d) (N := N) (G := G),
          |pe (plaquetteHolonomy A p)|
        ≤ ∑ _p : FiniteLatticeGeometry.P (d := d) (N := N) (G := G), B :=
          Finset.sum_le_sum fun p _ => hpe _
      _ = B * (Fintype.card (FiniteLatticeGeometry.P (d := d) (N := N) (G := G))) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
  calc -β * wilsonAction pe A ≤ |(-β) * wilsonAction pe A| := le_abs_self _
    _ = |β| * |wilsonAction pe A| := by rw [abs_mul, abs_neg]
    _ ≤ |β| * (B * (Fintype.card
          (FiniteLatticeGeometry.P (d := d) (N := N) (G := G)))) :=
        mul_le_mul_of_nonneg_left hS (abs_nonneg β)
    _ = |β| * B * (Fintype.card
          (FiniteLatticeGeometry.P (d := d) (N := N) (G := G))) := by ring

/-- **The partition function is positive, unconditionally** for bounded
measurable plaquette energies. -/
theorem partitionFunction_pos' [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ] {pe : G → ℝ}
    (hpe_meas : Measurable pe) {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ) :
    0 < partitionFunction (d := d) (N := N) μ pe β :=
  partitionFunction_pos μ pe β (integrable_boltzmann μ hpe_meas hpe β)

/-- **The Gibbs measure is a probability measure, unconditionally** for
bounded measurable plaquette energies. -/
theorem gibbsMeasure_isProbability' [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ] {pe : G → ℝ}
    (hpe_meas : Measurable pe) {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ) :
    IsProbabilityMeasure (gibbsMeasure (d := d) (N := N) μ pe β) :=
  gibbsMeasure_isProbability d N μ pe β (integrable_boltzmann μ hpe_meas hpe β)

/-! ### Locality: plaquette weights read only their support coordinates -/

/-- The positive-edge partner of an edge. -/
def ConcreteEdge.pos {d N : ℕ} (e : ConcreteEdge d N) : PosEdge d N :=
  ⟨{ e with sign := true }, rfl⟩

lemma ConcreteEdge.with_sign_true_eq {d N : ℕ} (e : ConcreteEdge d N)
    (he : e.sign = true) : ({ e with sign := true } : ConcreteEdge d N) = e := by
  obtain ⟨s, dir, sign⟩ := e
  cases he
  rfl

/-- Edge evaluations are determined by the positive-edge coordinates. -/
lemma config_eval_eq_of_pos {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    (A A' : GaugeConfig d N G) (e : ConcreteEdge d N)
    (h : configToPos A e.pos = configToPos A' e.pos) :
    A e = A' e := by
  have hval : A { e with sign := true } = A' { e with sign := true } := h
  by_cases he : e.sign = true
  · rw [← ConcreteEdge.with_sign_true_eq e he]
    exact hval
  · have he' : e.sign = false := by rwa [Bool.not_eq_true] at he
    rw [config_apply_neg A e he', config_apply_neg A' e he', hval]

/-- The **support** of a plaquette: the four positive-edge coordinates its
holonomy reads. -/
def plaquetteSupport {d N : ℕ} [NeZero N] (p : ConcretePlaquette d N) :
    Finset (PosEdge d N) :=
  {(p.edges 0).pos, (p.edges 1).pos, (p.edges 2).pos, (p.edges 3).pos}

/-- **Locality of the Mayer weight:** `f_p` depends only on the
configuration's positive-edge coordinates in `plaquetteSupport p`.  This is
the interface the polymer independence factorization (step 2) consumes. -/
lemma plaquetteWeight_congr {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G] (pe : G → ℝ) (β : ℝ)
    (p : ConcretePlaquette d N) {A A' : GaugeConfig d N G}
    (h : ∀ e ∈ plaquetteSupport p, configToPos A e = configToPos A' e) :
    plaquetteWeight pe β A p = plaquetteWeight pe β A' p := by
  have hhol : plaquetteHolonomy A p = plaquetteHolonomy A' p := by
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
  unfold plaquetteWeight
  rw [show (GaugeConfig.plaquetteHolonomy A p :
      G) = plaquetteHolonomy A' p from hhol]

/-- **Locality of Mayer-weight products** over a plaquette set `S`: they
depend only on the coordinates in the union of supports. -/
lemma prod_plaquetteWeight_congr {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G] (pe : G → ℝ) (β : ℝ)
    (S : Finset (ConcretePlaquette d N)) {A A' : GaugeConfig d N G}
    (h : ∀ e ∈ S.biUnion plaquetteSupport,
      configToPos A e = configToPos A' e) :
    ∏ p ∈ S, plaquetteWeight pe β A p
      = ∏ p ∈ S, plaquetteWeight pe β A' p := by
  classical
  refine Finset.prod_congr rfl fun p hp => ?_
  exact plaquetteWeight_congr pe β p fun e he =>
    h e (Finset.mem_biUnion.mpr ⟨p, hp, he⟩)

/-! ### The quantitative high-temperature estimate: `Z ≈ 1` -/

/-- Binomial subset-counting (local copy):
`∑_{c ⊆ univ} x^{|c|} = (x+1)^{#X}`. -/
private lemma sum_powerset_pow_card' {X : Type*} [Fintype X] [DecidableEq X]
    (x : ℝ) :
    ∑ c ∈ (Finset.univ : Finset X).powerset, x ^ c.card
      = (x + 1) ^ Fintype.card X := by
  rw [← Finset.card_univ, ← Finset.prod_const (x + 1), Finset.prod_add]
  exact Finset.sum_congr rfl fun t _ => by
    rw [Finset.prod_const, Finset.prod_const_one, mul_one]

/-- **The partition function is exponentially close to `1` at small
coupling:** `|Z − 1| ≤ e^{|β|·B·#plaquettes} − 1`, with the error controlled
entirely by the Mayer activities.  (The `S = ∅` term of the polymer-gas sum
is `1`; every other term is bounded by `(e^{|β|B}−1)^{|S|}`.) -/
theorem abs_partitionFunction_sub_one_le [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ] {pe : G → ℝ}
    (hpe_meas : Measurable pe) {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ) :
    |partitionFunction (d := d) (N := N) μ pe β - 1|
      ≤ ((Real.exp (|β| * B) - 1) + 1)
          ^ Fintype.card (FiniteLatticeGeometry.P (d := d) (N := N) (G := G))
        - 1 := by
  classical
  have hε0 : (0 : ℝ) ≤ Real.exp (|β| * B) - 1 := by
    have h1 : (1 : ℝ) ≤ Real.exp (|β| * B) := by
      rw [← Real.exp_zero]
      refine Real.exp_le_exp.mpr ?_
      have hB : (0 : ℝ) ≤ B := le_trans (abs_nonneg _) (hpe 1)
      positivity
    linarith
  rw [partitionFunction_eq_sum_plaquetteSets' μ hpe_meas hpe β]
  -- split off the `∅` term, which equals 1
  have hmem : (∅ : Finset (FiniteLatticeGeometry.P (d := d) (N := N) (G := G)))
      ∈ (Finset.univ :
        Finset (FiniteLatticeGeometry.P (d := d) (N := N) (G := G))).powerset :=
    Finset.empty_mem_powerset _
  have hsum := Finset.add_sum_erase _
    (fun S => ∫ A, ∏ p ∈ S, plaquetteWeight pe β A p
      ∂(gaugeMeasureFrom (d := d) (N := N) μ)) hmem
  beta_reduce at hsum
  have hemptyterm : ∫ A : GaugeConfig d N G,
      ∏ p ∈ (∅ : Finset (FiniteLatticeGeometry.P (d := d) (N := N) (G := G))),
        plaquetteWeight pe β A p
      ∂(gaugeMeasureFrom (d := d) (N := N) μ) = 1 := by
    simp [measure_univ]
  rw [← hsum, hemptyterm, add_sub_cancel_left]
  -- bound the remaining sum term by term
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hbound : ∀ S : Finset (FiniteLatticeGeometry.P (d := d) (N := N) (G := G)),
      |∫ A, ∏ p ∈ S, plaquetteWeight pe β A p
        ∂(gaugeMeasureFrom (d := d) (N := N) μ)|
      ≤ (Real.exp (|β| * B) - 1) ^ S.card := by
    intro S
    have h := MeasureTheory.norm_integral_le_of_norm_le_const
      (μ := gaugeMeasureFrom (d := d) (N := N) μ)
      (f := fun A : GaugeConfig d N G => ∏ p ∈ S, plaquetteWeight pe β A p)
      (C := (Real.exp (|β| * B) - 1) ^ S.card) ?_
    · rw [Real.norm_eq_abs] at h
      simpa [measure_univ] using h
    · refine MeasureTheory.ae_of_all _ fun A => ?_
      rw [Real.norm_eq_abs, Finset.abs_prod]
      calc ∏ p ∈ S, |plaquetteWeight pe β A p|
          ≤ ∏ _p ∈ S, (Real.exp (|β| * B) - 1) :=
            Finset.prod_le_prod (fun p _ => abs_nonneg _)
              (fun p _ => abs_plaquetteWeight_le pe β A p hpe)
        _ = (Real.exp (|β| * B) - 1) ^ S.card := by rw [Finset.prod_const]
  calc ∑ S ∈ ((Finset.univ :
        Finset (FiniteLatticeGeometry.P (d := d) (N := N) (G := G))).powerset).erase ∅,
        |∫ A, ∏ p ∈ S, plaquetteWeight pe β A p
          ∂(gaugeMeasureFrom (d := d) (N := N) μ)|
      ≤ ∑ S ∈ ((Finset.univ :
          Finset (FiniteLatticeGeometry.P (d := d) (N := N) (G := G))).powerset).erase ∅,
          (Real.exp (|β| * B) - 1) ^ S.card :=
        Finset.sum_le_sum fun S _ => hbound S
    _ = ((Real.exp (|β| * B) - 1) + 1)
          ^ Fintype.card (FiniteLatticeGeometry.P (d := d) (N := N) (G := G))
        - 1 := by
        have h2 := Finset.add_sum_erase _
          (fun S : Finset (FiniteLatticeGeometry.P (d := d) (N := N) (G := G)) =>
            (Real.exp (|β| * B) - 1) ^ S.card) hmem
        have h3 := sum_powerset_pow_card'
          (X := FiniteLatticeGeometry.P (d := d) (N := N) (G := G))
          (Real.exp (|β| * B) - 1)
        simp only [Finset.card_empty, pow_zero] at h2
        linarith

/-- **Quantitative positivity:** if the total high-temperature error is
below `1` — i.e. `(e^{|β|B})^{#P} < 2` — then `Z > 0`. -/
theorem partitionFunction_pos_of_small [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ] {pe : G → ℝ}
    (hpe_meas : Measurable pe) {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (hsmall : ((Real.exp (|β| * B) - 1) + 1)
        ^ Fintype.card (FiniteLatticeGeometry.P (d := d) (N := N) (G := G))
      < 2) :
    0 < partitionFunction (d := d) (N := N) μ pe β := by
  have h := abs_partitionFunction_sub_one_le (d := d) (N := N)
    μ hpe_meas hpe β
  have h2 := abs_le.mp h
  linarith [h2.1]

end Integrability

end YangMills
