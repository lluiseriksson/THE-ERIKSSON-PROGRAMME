/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.L1_GibbsMeasure.PolymerExpansion

/-!
# Polymer representation, step 2 (core) — independence over disjoint supports

The abstract factorization that makes polymer activities multiplicative: for
a product probability measure, the integral of a product of two observables
**depending on disjoint coordinate sets** factorizes:

  `∫ F·G  =  ∫F · ∫G`.

Proof: split the coordinate space along the predicate
(`MeasurableEquiv.piEquivPiSubtypeProd`, measure-preserving onto the product
of the two marginal product measures), observe each factor depends on only
one block, and apply the unconditional product-integral identity
(`integral_prod_mul`).  No integrability hypotheses are needed.

Applied to the lattice (next slice): Mayer-weight products over plaquette
sets with disjoint supports (`prod_plaquetteWeight_congr` is exactly the
dependency hypothesis) have multiplicative gauge expectations — the polymer
activity factorization over connected components.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills

open MeasureTheory

/-- **Two-block independence for product measures:** if `F` depends only on
the coordinates satisfying `p` and `G` only on those violating it, then
`∫ F·G = ∫F · ∫G` under any product probability measure.  No integrability
hypotheses. -/
theorem integral_mul_of_disjoint_deps {ι : Type*} [Fintype ι]
    {β : Type*} [MeasurableSpace β] [Nonempty β]
    (μ : Measure β) [IsProbabilityMeasure μ]
    (p : ι → Prop) [DecidablePred p] (F G : (ι → β) → ℝ)
    (hF : ∀ x y : ι → β, (∀ i, p i → x i = y i) → F x = F y)
    (hG : ∀ x y : ι → β, (∀ i, ¬ p i → x i = y i) → G x = G y) :
    ∫ x, F x * G x ∂(Measure.pi fun _ : ι => μ)
      = (∫ x, F x ∂(Measure.pi fun _ : ι => μ)) *
        ∫ x, G x ∂(Measure.pi fun _ : ι => μ) := by
  classical
  obtain ⟨b₀⟩ := (inferInstance : Nonempty β)
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => β) p with hedef
  have hmp : MeasurePreserving e (Measure.pi fun _ : ι => μ)
      ((Measure.pi fun _ : {i // p i} => μ).prod
        (Measure.pi fun _ : {i // ¬ p i} => μ)) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) p
  -- coordinates of the inverse equivalence
  have hcoord : ∀ (a : {i // p i} → β) (b : {i // ¬ p i} → β) (i : ι),
      e.symm (a, b) i = if h : p i then a ⟨i, h⟩ else b ⟨i, h⟩ := by
    intro a b i
    simp [hedef, MeasurableEquiv.piEquivPiSubtypeProd,
      Equiv.piEquivPiSubtypeProd]
  -- the block restrictions
  set F₁ : ({i // p i} → β) → ℝ := fun a => F (e.symm (a, fun _ => b₀))
    with hF₁def
  set G₁ : ({i // ¬ p i} → β) → ℝ := fun b => G (e.symm (fun _ => b₀, b))
    with hG₁def
  have hFsplit : ∀ (a : {i // p i} → β) (b : {i // ¬ p i} → β),
      F (e.symm (a, b)) = F₁ a := by
    intro a b
    refine hF _ _ fun i hi => ?_
    rw [hcoord, hcoord, dif_pos hi, dif_pos hi]
  have hGsplit : ∀ (a : {i // p i} → β) (b : {i // ¬ p i} → β),
      G (e.symm (a, b)) = G₁ b := by
    intro a b
    refine hG _ _ fun i hi => ?_
    rw [hcoord, hcoord, dif_neg hi, dif_neg hi]
  -- integral transport along the (inverse) equivalence
  have htrans : ∀ H : (ι → β) → ℝ,
      ∫ x, H x ∂(Measure.pi fun _ : ι => μ)
        = ∫ z, H (e.symm z)
            ∂((Measure.pi fun _ : {i // p i} => μ).prod
              (Measure.pi fun _ : {i // ¬ p i} => μ)) := by
    intro H
    have hmp' := hmp.symm e
    rw [← hmp'.map_eq, MeasureTheory.integral_map_equiv]
  -- the three transported integrals and the product split
  rw [htrans (fun x => F x * G x), htrans F, htrans G]
  have hptFG : (fun z : ({i // p i} → β) × ({i // ¬ p i} → β) =>
      F (e.symm z) * G (e.symm z)) = fun z => F₁ z.1 * G₁ z.2 := by
    funext z
    rw [show z = (z.1, z.2) from rfl, hFsplit z.1 z.2, hGsplit z.1 z.2]
  have hptF : (fun z : ({i // p i} → β) × ({i // ¬ p i} → β) =>
      F (e.symm z)) = fun z => F₁ z.1 := by
    funext z
    rw [show z = (z.1, z.2) from rfl, hFsplit z.1 z.2]
  have hptG : (fun z : ({i // p i} → β) × ({i // ¬ p i} → β) =>
      G (e.symm z)) = fun z => G₁ z.2 := by
    funext z
    rw [show z = (z.1, z.2) from rfl, hGsplit z.1 z.2]
  rw [hptFG, hptF, hptG, MeasureTheory.integral_prod_mul]
  congr 1
  · have h1 := MeasureTheory.integral_prod_mul
      (μ := Measure.pi fun _ : {i // p i} => μ)
      (ν := Measure.pi fun _ : {i // ¬ p i} => μ) F₁ (fun _ => (1 : ℝ))
    simp only [mul_one] at h1
    rw [h1]
    simp
  · have h1 := MeasureTheory.integral_prod_mul
      (μ := Measure.pi fun _ : {i // p i} => μ)
      (ν := Measure.pi fun _ : {i // ¬ p i} => μ) (fun _ => (1 : ℝ)) G₁
    simp only [one_mul] at h1
    rw [h1]
    simp

/-- **Polymer activity factorization:** Mayer-weight products over plaquette
sets with **disjoint supports** have multiplicative gauge expectations —
`∫ (∏_S f_p)(∏_T f_p) = ∫∏_S · ∫∏_T`.  The locality interface
(`prod_plaquetteWeight_congr`) supplies the dependency hypotheses of the
abstract two-block factorization. -/
theorem integral_prod_plaquetteWeight_mul_of_disjoint
    {d N : ℕ} [NeZero d] [NeZero N] {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ] (pe : G → ℝ) (β : ℝ)
    (S T : Finset (ConcretePlaquette d N))
    (hdisj : Disjoint (S.biUnion plaquetteSupport)
      (T.biUnion plaquetteSupport)) :
    ∫ A, (∏ p ∈ S, plaquetteWeight pe β A p) *
        ∏ p ∈ T, plaquetteWeight pe β A p
      ∂(gaugeMeasureFrom (d := d) (N := N) μ)
    = (∫ A, ∏ p ∈ S, plaquetteWeight pe β A p
        ∂(gaugeMeasureFrom (d := d) (N := N) μ)) *
      ∫ A, ∏ p ∈ T, plaquetteWeight pe β A p
        ∂(gaugeMeasureFrom (d := d) (N := N) μ) := by
  classical
  haveI : Nonempty G := ⟨1⟩
  -- transport to the positive-edge coordinates
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
  -- the abstract two-block factorization, fed by locality
  refine integral_mul_of_disjoint_deps μ
    (fun e => e ∈ S.biUnion plaquetteSupport) _ _ ?_ ?_
  · intro x y hxy
    refine prod_plaquetteWeight_congr pe β S ?_
    intro e he
    rw [show configToPos (gaugeConfigMEquiv x) = x from
        (gaugeConfigEquiv (d := d) (N := N) (G := G)).left_inv x,
      show configToPos (gaugeConfigMEquiv y) = y from
        (gaugeConfigEquiv (d := d) (N := N) (G := G)).left_inv y]
    exact hxy e he
  · intro x y hxy
    refine prod_plaquetteWeight_congr pe β T ?_
    intro e he
    rw [show configToPos (gaugeConfigMEquiv x) = x from
        (gaugeConfigEquiv (d := d) (N := N) (G := G)).left_inv x,
      show configToPos (gaugeConfigMEquiv y) = y from
        (gaugeConfigEquiv (d := d) (N := N) (G := G)).left_inv y]
    exact hxy e fun heS => Finset.disjoint_left.mp hdisj heS he

/-- **Iterated polymer factorization:** over a family of plaquette sets with
pairwise-disjoint supports, the gauge expectation of the full Mayer product
is the product of the per-component expectations —
`∫ ∏_{c ∈ C} ∏_{p ∈ c} f_p = ∏_{c ∈ C} ∫ ∏_{p ∈ c} f_p`.
This is the multiplicativity of polymer activities over connected
components. -/
theorem integral_prod_prod_plaquetteWeight_of_pairwiseDisjoint
    {d N : ℕ} [NeZero d] [NeZero N] {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ] (pe : G → ℝ) (β : ℝ)
    (C : Finset (Finset (ConcretePlaquette d N)))
    (hdisj : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' →
      Disjoint (c.biUnion plaquetteSupport) (c'.biUnion plaquetteSupport))
    (hsets : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → Disjoint c c') :
    ∫ A, ∏ c ∈ C, ∏ p ∈ c, plaquetteWeight pe β A p
      ∂(gaugeMeasureFrom (d := d) (N := N) μ)
    = ∏ c ∈ C, ∫ A, ∏ p ∈ c, plaquetteWeight pe β A p
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
    -- the rest of the family as a single plaquette set
    have hbig : ∀ A : GaugeConfig d N G,
        ∏ c' ∈ C', ∏ p ∈ c', plaquetteWeight pe β A p
          = ∏ p ∈ C'.biUnion id, plaquetteWeight pe β A p := by
      intro A
      exact (Finset.prod_biUnion (fun a ha b hb hab =>
        hsets' a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) hab)).symm
    -- support disjointness of `c` against the union of the rest
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
        ∏ c' ∈ insert c C', ∏ p ∈ c', plaquetteWeight pe β A p
          = (∏ p ∈ c, plaquetteWeight pe β A p) *
            ∏ c' ∈ C', ∏ p ∈ c', plaquetteWeight pe β A p :=
      fun A => Finset.prod_insert hc
    simp only [hins]
    have hsplit : ∫ A, (∏ p ∈ c, plaquetteWeight pe β A p) *
          ∏ c' ∈ C', ∏ p ∈ c', plaquetteWeight pe β A p
        ∂(gaugeMeasureFrom (d := d) (N := N) μ)
        = (∫ A, ∏ p ∈ c, plaquetteWeight pe β A p
            ∂(gaugeMeasureFrom (d := d) (N := N) μ)) *
          ∫ A, ∏ c' ∈ C', ∏ p ∈ c', plaquetteWeight pe β A p
            ∂(gaugeMeasureFrom (d := d) (N := N) μ) := by
      simp only [hbig]
      exact integral_prod_plaquetteWeight_mul_of_disjoint μ pe β
        c (C'.biUnion id) hcd
    rw [hsplit, ih hdisj' hsets']

end YangMills
