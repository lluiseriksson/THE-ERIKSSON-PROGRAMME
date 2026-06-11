/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.L1_GibbsMeasure.PolymerExpansion
import YangMills.L1_GibbsMeasure.PolymerFactorization

/-!
# The weighted lattice gas (B2, brick W1)

The covariance identity of the correlation chain
(`docs/CLUSTER-CORRELATION-PLAN.md` §2e/B2) needs the `Z = Ξ` machinery
not just for the Mayer weights `f_p = e^{-β·E(hol_p)} − 1` but for
**deformed** weight families: a multiplicative local observable
`F = ∏_{p∈S_F}(1 + s·g_p)` satisfies
`F·∏_p(1+f_p) = ∏_p(1+f̃_p)` with `f̃` again local.  So this file
generalizes the gas foundations from `plaquetteWeight pe β` to an
arbitrary **local weight family** `w`:

* `IsLocalWeight` — `w A p` depends only on `A`'s edges in
  `plaquetteSupport p` (the Mayer weights qualify:
  `isLocalWeight_plaquetteWeight`);
* `prod_weight_congr`, `integral_prod_weight_mul_of_disjoint`,
  `integral_prod_prod_weight_of_pairwiseDisjoint` — the locality and
  factorization interface, weight-general (the abstract two-block
  engine `integral_mul_of_disjoint_deps` was already general);
* `weightedPartition` `Z[w] = ∫ ∏_p (1 + w_p)`, its binomial expansion
  `weightedPartition_eq_sum`, integrability from boundedness
  (`integrable_prod_weight`), and the Wilson instantiation
  `weightedPartition_plaquetteWeight : Z[f] = Z`.

Next bricks: W2 — the weighted polymer system and `Z[w] = Ξ[w]`
(verbatim transport of `partitionFunction_eq_partition`); W3 — the KP
criterion under `‖w‖_∞ ≤ δ`; W4 — the covariance identity.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills

open MeasureTheory

variable {d N : ℕ} [NeZero d] [NeZero N]
variable {G : Type*} [Group G] [MeasurableSpace G]

/-- **Locality of a weight family:** `w A p` depends only on the
configuration's positive-edge coordinates in `plaquetteSupport p`. -/
def IsLocalWeight (w : GaugeConfig d N G → ConcretePlaquette d N → ℝ) :
    Prop :=
  ∀ (p : ConcretePlaquette d N) (A A' : GaugeConfig d N G),
    (∀ e ∈ plaquetteSupport p, configToPos A e = configToPos A' e) →
    w A p = w A' p

/-- The Mayer weights are local. -/
lemma isLocalWeight_plaquetteWeight (pe : G → ℝ) (β : ℝ) :
    IsLocalWeight (fun (A : GaugeConfig d N G)
      (p : ConcretePlaquette d N) => plaquetteWeight pe β A p) :=
  fun p A A' h => plaquetteWeight_congr pe β p h

/-- Locality of weight products over a plaquette set. -/
lemma prod_weight_congr
    {w : GaugeConfig d N G → ConcretePlaquette d N → ℝ}
    (hloc : IsLocalWeight (d := d) (N := N) (G := G) w)
    (S : Finset (ConcretePlaquette d N)) {A A' : GaugeConfig d N G}
    (h : ∀ e ∈ S.biUnion plaquetteSupport,
      configToPos A e = configToPos A' e) :
    ∏ p ∈ S, w A p = ∏ p ∈ S, w A' p := by
  classical
  refine Finset.prod_congr rfl fun p hp => ?_
  exact hloc p A A' fun e he =>
    h e (Finset.mem_biUnion.mpr ⟨p, hp, he⟩)

/-- **Two-block factorization for local weight families:** products over
plaquette sets with disjoint supports have multiplicative gauge
expectations. -/
theorem integral_prod_weight_mul_of_disjoint
    (μ : Measure G) [IsProbabilityMeasure μ]
    {w : GaugeConfig d N G → ConcretePlaquette d N → ℝ}
    (hloc : IsLocalWeight (d := d) (N := N) (G := G) w)
    (S T : Finset (ConcretePlaquette d N))
    (hdisj : Disjoint (S.biUnion plaquetteSupport)
      (T.biUnion plaquetteSupport)) :
    ∫ A, (∏ p ∈ S, w A p) * ∏ p ∈ T, w A p
      ∂(gaugeMeasureFrom (d := d) (N := N) μ)
    = (∫ A, ∏ p ∈ S, w A p
        ∂(gaugeMeasureFrom (d := d) (N := N) μ)) *
      ∫ A, ∏ p ∈ T, w A p
        ∂(gaugeMeasureFrom (d := d) (N := N) μ) := by
  classical
  haveI : Nonempty G := ⟨1⟩
  have htrans : ∀ H : GaugeConfig d N G → ℝ,
      ∫ A, H A ∂(gaugeMeasureFrom (d := d) (N := N) μ)
        = ∫ x, H (gaugeConfigMEquiv x)
            ∂(Measure.pi fun _ : PosEdge d N => μ) := by
    intro H
    have hmeas : gaugeMeasureFrom (d := d) (N := N) μ
        = Measure.map (gaugeConfigMEquiv (d := d) (N := N) (G := G))
            (Measure.pi fun _ : PosEdge d N => μ) := rfl
    rw [hmeas, MeasureTheory.integral_map_equiv]
  rw [htrans, htrans, htrans]
  refine integral_mul_of_disjoint_deps μ
    (fun e => e ∈ S.biUnion plaquetteSupport) _ _ ?_ ?_
  · intro x y hxy
    refine prod_weight_congr hloc S ?_
    intro e he
    rw [show configToPos (gaugeConfigMEquiv x) = x from
        (gaugeConfigEquiv (d := d) (N := N) (G := G)).left_inv x,
      show configToPos (gaugeConfigMEquiv y) = y from
        (gaugeConfigEquiv (d := d) (N := N) (G := G)).left_inv y]
    exact hxy e he
  · intro x y hxy
    refine prod_weight_congr hloc T ?_
    intro e he
    rw [show configToPos (gaugeConfigMEquiv x) = x from
        (gaugeConfigEquiv (d := d) (N := N) (G := G)).left_inv x,
      show configToPos (gaugeConfigMEquiv y) = y from
        (gaugeConfigEquiv (d := d) (N := N) (G := G)).left_inv y]
    exact hxy e fun heS => Finset.disjoint_left.mp hdisj heS he

/-- **Iterated factorization for local weight families** over pairwise
support-disjoint plaquette sets. -/
theorem integral_prod_prod_weight_of_pairwiseDisjoint
    (μ : Measure G) [IsProbabilityMeasure μ]
    {w : GaugeConfig d N G → ConcretePlaquette d N → ℝ}
    (hloc : IsLocalWeight (d := d) (N := N) (G := G) w)
    (C : Finset (Finset (ConcretePlaquette d N)))
    (hdisj : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' →
      Disjoint (c.biUnion plaquetteSupport) (c'.biUnion plaquetteSupport))
    (hsets : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → Disjoint c c') :
    ∫ A, ∏ c ∈ C, ∏ p ∈ c, w A p
      ∂(gaugeMeasureFrom (d := d) (N := N) μ)
    = ∏ c ∈ C, ∫ A, ∏ p ∈ c, w A p
        ∂(gaugeMeasureFrom (d := d) (N := N) μ) := by
  classical
  induction C using Finset.induction_on with
  | empty => simp
  | insert c C' hc ih =>
    have hdisj' : ∀ a ∈ C', ∀ b ∈ C', a ≠ b →
        Disjoint (a.biUnion plaquetteSupport) (b.biUnion plaquetteSupport) :=
      fun a ha b hb hab => hdisj a (Finset.mem_insert_of_mem ha)
        b (Finset.mem_insert_of_mem hb) hab
    have hsets' : ∀ a ∈ C', ∀ b ∈ C', a ≠ b → Disjoint a b :=
      fun a ha b hb hab => hsets a (Finset.mem_insert_of_mem ha)
        b (Finset.mem_insert_of_mem hb) hab
    have hbig : ∀ A : GaugeConfig d N G,
        ∏ c' ∈ C', ∏ p ∈ c', w A p
          = ∏ p ∈ C'.biUnion id, w A p := by
      intro A
      exact (Finset.prod_biUnion (fun a ha b hb hab =>
        hsets' a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) hab)).symm
    have hcd : Disjoint (c.biUnion plaquetteSupport)
        ((C'.biUnion id).biUnion plaquetteSupport) := by
      rw [Finset.biUnion_biUnion]
      rw [Finset.disjoint_biUnion_right]
      intro c' hc'
      have hne : c ≠ c' := fun h => hc (h ▸ hc')
      have := hdisj c (Finset.mem_insert_self c C')
        c' (Finset.mem_insert_of_mem hc') hne
      rw [Finset.disjoint_biUnion_right] at this ⊢
      intro p hp
      exact this p hp
    rw [Finset.prod_insert hc]
    have hins : ∀ A : GaugeConfig d N G,
        ∏ c' ∈ insert c C', ∏ p ∈ c', w A p
          = (∏ p ∈ c, w A p) * ∏ c' ∈ C', ∏ p ∈ c', w A p :=
      fun A => Finset.prod_insert hc
    simp only [hins]
    have hsplit : ∫ A, (∏ p ∈ c, w A p) * ∏ c' ∈ C', ∏ p ∈ c', w A p
        ∂(gaugeMeasureFrom (d := d) (N := N) μ)
        = (∫ A, ∏ p ∈ c, w A p
            ∂(gaugeMeasureFrom (d := d) (N := N) μ)) *
          ∫ A, ∏ c' ∈ C', ∏ p ∈ c', w A p
            ∂(gaugeMeasureFrom (d := d) (N := N) μ) := by
      simp only [hbig]
      exact integral_prod_weight_mul_of_disjoint μ hloc
        c (C'.biUnion id) hcd
    rw [hsplit, ih hdisj' hsets']

/-! ### The weighted partition function and its binomial expansion -/

/-- The **weighted partition function** `Z[w] = ∫ ∏_p (1 + w_p)`.
At `w = plaquetteWeight pe β` this is the Wilson partition function. -/
noncomputable def weightedPartition (μ : Measure G)
    (w : GaugeConfig d N G → ConcretePlaquette d N → ℝ) : ℝ :=
  ∫ A, ∏ p : ConcretePlaquette d N, (1 + w A p)
    ∂(gaugeMeasureFrom (d := d) (N := N) μ)

/-- The binomial expansion of the weighted Boltzmann product. -/
lemma prod_one_add_eq_sum
    (w : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    (A : GaugeConfig d N G) :
    ∏ p : ConcretePlaquette d N, (1 + w A p)
      = ∑ S ∈ (Finset.univ : Finset (ConcretePlaquette d N)).powerset,
          ∏ p ∈ S, w A p := by
  classical
  have hcomm : ∀ p ∈ (Finset.univ : Finset (ConcretePlaquette d N)),
      1 + w A p = w A p + 1 := fun p _ => by ring
  rw [Finset.prod_congr rfl hcomm, Finset.prod_add]
  exact Finset.sum_congr rfl fun t _ => by
    rw [Finset.prod_const_one, mul_one]

/-- Bounded measurable weight products are integrable. -/
lemma integrable_prod_weight (μ : Measure G) [IsProbabilityMeasure μ]
    {w : GaugeConfig d N G → ConcretePlaquette d N → ℝ}
    (hmeas : ∀ p : ConcretePlaquette d N,
      Measurable (fun A : GaugeConfig d N G => w A p))
    {δ : ℝ} (hbd : ∀ A p, |w A p| ≤ δ)
    (S : Finset (ConcretePlaquette d N)) :
    Integrable (fun A : GaugeConfig d N G => ∏ p ∈ S, w A p)
      (gaugeMeasureFrom (d := d) (N := N) μ) := by
  classical
  have hm : Measurable (fun A : GaugeConfig d N G => ∏ p ∈ S, w A p) :=
    Finset.measurable_prod _ fun p _ => hmeas p
  refine (MeasureTheory.integrable_const (δ ^ S.card)).mono'
    hm.aestronglyMeasurable ?_
  refine MeasureTheory.ae_of_all _ fun A => ?_
  rw [Real.norm_eq_abs, Finset.abs_prod]
  calc ∏ p ∈ S, |w A p|
      ≤ ∏ _p ∈ S, δ :=
        Finset.prod_le_prod (fun p _ => abs_nonneg _)
          (fun p _ => hbd A p)
    _ = δ ^ S.card := by rw [Finset.prod_const]

/-- **The weighted polymer-gas sum:** `Z[w] = ∑_S ∫ ∏_{p∈S} w_p` for
bounded measurable local weight families. -/
theorem weightedPartition_eq_sum (μ : Measure G) [IsProbabilityMeasure μ]
    {w : GaugeConfig d N G → ConcretePlaquette d N → ℝ}
    (hmeas : ∀ p : ConcretePlaquette d N,
      Measurable (fun A : GaugeConfig d N G => w A p))
    {δ : ℝ} (hbd : ∀ A p, |w A p| ≤ δ) :
    weightedPartition (d := d) (N := N) μ w
      = ∑ S ∈ (Finset.univ : Finset (ConcretePlaquette d N)).powerset,
          ∫ A, ∏ p ∈ S, w A p
            ∂(gaugeMeasureFrom (d := d) (N := N) μ) := by
  classical
  unfold weightedPartition
  rw [show (fun A : GaugeConfig d N G =>
      ∏ p : ConcretePlaquette d N, (1 + w A p))
      = fun A => ∑ S ∈ (Finset.univ :
          Finset (ConcretePlaquette d N)).powerset, ∏ p ∈ S, w A p
    from funext fun A => prod_one_add_eq_sum w A]
  exact MeasureTheory.integral_finset_sum _ fun S _ =>
    integrable_prod_weight μ hmeas hbd S

/-- At the Mayer weights, the weighted partition function is the Wilson
partition function. -/
lemma weightedPartition_plaquetteWeight (μ : Measure G)
    [IsProbabilityMeasure μ] (pe : G → ℝ) (β : ℝ) :
    weightedPartition (d := d) (N := N) μ
      (fun A p => plaquetteWeight pe β A p)
      = partitionFunction (d := d) (N := N) μ pe β := by
  classical
  unfold weightedPartition partitionFunction
  congr 1
  funext A
  rw [boltzmann_eq_sum_plaquetteSets pe β A]
  exact prod_one_add_eq_sum (fun A p => plaquetteWeight pe β A p) A

/-! ### Deformed weights (B2, brick W4a)

A multiplicative local observable `F = ∏_{p∈T}(1+g_p)` absorbs into the
weights: `F·∏_p(1+w_p) = ∏_p(1+w̃_p)` with `w̃ = deformWeight w g T`.
So `⟨F⟩·Z[w] = Z[w̃]` — the numerators of Gibbs expectations of
multiplicative observables are themselves weighted partition functions,
and the whole `Z = Ξ = exp(K)` chain applies to them. -/

open Classical in
/-- The **multiplicative deformation** of a weight family on a region:
`1 + w̃_p = (1+w_p)(1+g_p)` for `p ∈ T`, `w̃_p = w_p` otherwise. -/
noncomputable def deformWeight
    (w g : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    (T : Finset (ConcretePlaquette d N)) :
    GaugeConfig d N G → ConcretePlaquette d N → ℝ :=
  fun A p => if p ∈ T then w A p + g A p + w A p * g A p else w A p

open Classical in
lemma one_add_deformWeight_of_mem
    {w g : GaugeConfig d N G → ConcretePlaquette d N → ℝ}
    {T : Finset (ConcretePlaquette d N)}
    {A : GaugeConfig d N G} {p : ConcretePlaquette d N} (hp : p ∈ T) :
    1 + deformWeight w g T A p = (1 + w A p) * (1 + g A p) := by
  unfold deformWeight
  rw [if_pos hp]
  ring

open Classical in
lemma deformWeight_of_not_mem
    {w g : GaugeConfig d N G → ConcretePlaquette d N → ℝ}
    {T : Finset (ConcretePlaquette d N)}
    {A : GaugeConfig d N G} {p : ConcretePlaquette d N} (hp : p ∉ T) :
    deformWeight w g T A p = w A p := by
  unfold deformWeight
  rw [if_neg hp]

open Classical in
/-- Deformations of local weight families are local. -/
lemma isLocalWeight_deformWeight
    {w g : GaugeConfig d N G → ConcretePlaquette d N → ℝ}
    (hw : IsLocalWeight (d := d) (N := N) (G := G) w)
    (hg : IsLocalWeight (d := d) (N := N) (G := G) g)
    (T : Finset (ConcretePlaquette d N)) :
    IsLocalWeight (d := d) (N := N) (G := G) (deformWeight w g T) := by
  intro p A A' h
  unfold deformWeight
  by_cases hp : p ∈ T
  · rw [if_pos hp, if_pos hp, hw p A A' h, hg p A A' h]
  · rw [if_neg hp, if_neg hp, hw p A A' h]

open Classical in
/-- Deformed weights stay uniformly bounded. -/
lemma abs_deformWeight_le
    {w g : GaugeConfig d N G → ConcretePlaquette d N → ℝ}
    {δw δg : ℝ} (hw : ∀ A p, |w A p| ≤ δw) (hg : ∀ A p, |g A p| ≤ δg)
    (T : Finset (ConcretePlaquette d N))
    (A : GaugeConfig d N G) (p : ConcretePlaquette d N) :
    |deformWeight w g T A p| ≤ δw + δg + δw * δg := by
  have hδw : (0 : ℝ) ≤ δw := le_trans (abs_nonneg _) (hw A p)
  have hδg : (0 : ℝ) ≤ δg := le_trans (abs_nonneg _) (hg A p)
  unfold deformWeight
  by_cases hp : p ∈ T
  · rw [if_pos hp]
    calc |w A p + g A p + w A p * g A p|
        ≤ |w A p + g A p| + |w A p * g A p| := abs_add_le _ _
      _ ≤ (|w A p| + |g A p|) + |w A p| * |g A p| := by
          rw [abs_mul]
          exact add_le_add (abs_add_le (w A p) (g A p)) le_rfl
      _ ≤ (δw + δg) + δw * δg := by
          refine add_le_add (add_le_add (hw A p) (hg A p)) ?_
          exact mul_le_mul (hw A p) (hg A p) (abs_nonneg _) hδw
      _ = δw + δg + δw * δg := rfl
  · rw [if_neg hp]
    have h1 : (0 : ℝ) ≤ δg + δw * δg := by positivity
    calc |w A p| ≤ δw := hw A p
      _ ≤ δw + (δg + δw * δg) := le_add_of_nonneg_right h1
      _ = δw + δg + δw * δg := by ring

open Classical in
/-- Deformed weights stay measurable. -/
lemma measurable_deformWeight
    {w g : GaugeConfig d N G → ConcretePlaquette d N → ℝ}
    (hw : ∀ p : ConcretePlaquette d N,
      Measurable (fun A : GaugeConfig d N G => w A p))
    (hg : ∀ p : ConcretePlaquette d N,
      Measurable (fun A : GaugeConfig d N G => g A p))
    (T : Finset (ConcretePlaquette d N))
    (p : ConcretePlaquette d N) :
    Measurable (fun A : GaugeConfig d N G => deformWeight w g T A p) := by
  unfold deformWeight
  by_cases hp : p ∈ T
  · simp only [if_pos hp]
    exact ((hw p).add (hg p)).add ((hw p).mul (hg p))
  · simp only [if_neg hp]
    exact hw p

open Classical in
/-- **The absorption identity (W4a):** the deformed partition function
is the numerator of the Gibbs expectation of the multiplicative local
observable `∏_{p∈T}(1+g_p)`. -/
theorem weightedPartition_deform (μ : Measure G) [IsProbabilityMeasure μ]
    (w g : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    (T : Finset (ConcretePlaquette d N)) :
    weightedPartition (d := d) (N := N) μ (deformWeight w g T)
      = ∫ A, (∏ p ∈ T, (1 + g A p)) *
          ∏ p : ConcretePlaquette d N, (1 + w A p)
          ∂(gaugeMeasureFrom (d := d) (N := N) μ) := by
  classical
  unfold weightedPartition
  congr 1
  funext A
  calc ∏ p : ConcretePlaquette d N, (1 + deformWeight w g T A p)
      = ∏ p : ConcretePlaquette d N,
          ((1 + w A p) * (if p ∈ T then 1 + g A p else 1)) := by
        refine Finset.prod_congr rfl fun p _ => ?_
        by_cases hp : p ∈ T
        · rw [if_pos hp, one_add_deformWeight_of_mem hp]
        · rw [if_neg hp, mul_one, deformWeight_of_not_mem hp]
    _ = (∏ p : ConcretePlaquette d N, (1 + w A p)) *
        ∏ p : ConcretePlaquette d N, (if p ∈ T then 1 + g A p else 1) :=
        Finset.prod_mul_distrib
    _ = (∏ p : ConcretePlaquette d N, (1 + w A p)) *
        ∏ p ∈ T, (1 + g A p) := by
        rw [Finset.prod_ite_mem, Finset.univ_inter]
    _ = (∏ p ∈ T, (1 + g A p)) *
        ∏ p : ConcretePlaquette d N, (1 + w A p) := mul_comm _ _

open Classical in
/-- Off the left region, deforming on a union is deforming on the right
region alone — the per-plaquette seed of the covariance cancellation. -/
lemma deformWeight_union_of_not_mem_left
    {w g : GaugeConfig d N G → ConcretePlaquette d N → ℝ}
    {S T : Finset (ConcretePlaquette d N)}
    {A : GaugeConfig d N G} {p : ConcretePlaquette d N} (hp : p ∉ S) :
    deformWeight w g (S ∪ T) A p = deformWeight w g T A p := by
  unfold deformWeight
  by_cases hpT : p ∈ T
  · rw [if_pos (Finset.mem_union_right _ hpT), if_pos hpT]
  · rw [if_neg (fun h => (Finset.mem_union.mp h).elim hp hpT),
      if_neg hpT]

open Classical in
/-- Off the right region, symmetrically. -/
lemma deformWeight_union_of_not_mem_right
    {w g : GaugeConfig d N G → ConcretePlaquette d N → ℝ}
    {S T : Finset (ConcretePlaquette d N)}
    {A : GaugeConfig d N G} {p : ConcretePlaquette d N} (hp : p ∉ T) :
    deformWeight w g (S ∪ T) A p = deformWeight w g S A p := by
  unfold deformWeight
  by_cases hpS : p ∈ S
  · rw [if_pos (Finset.mem_union_left _ hpS), if_pos hpS]
  · rw [if_neg (fun h => (Finset.mem_union.mp h).elim hpS hp),
      if_neg hpS]

end YangMills
