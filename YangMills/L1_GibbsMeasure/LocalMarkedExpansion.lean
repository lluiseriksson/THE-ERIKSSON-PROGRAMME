/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.L1_GibbsMeasure.LocalObservableSubstrate
import YangMills.L1_GibbsMeasure.RestrictedGate

/-!
# Exact marked expansion for arbitrary edge-local observables

This file generalizes the loop-tagged expansion of `SupportFactorization` from
observables of the form `φ (wilsonLine A es)` to an arbitrary complex
observable satisfying `DependsOnPos F SF`.

The marked plaquette set is `nearLoop es S`: it is the union of **all**
connected components of `S` whose positive-edge support meets `SF`.  It need
not be connected.  This is essential: two mutually disjoint plaquette
components can meet two different edges of a local observable, and an
arbitrary kernel can couple the corresponding Haar variables.

The terminal theorem in the first section,
`integral_localSupport_tagged_expansion`, is an exact finite-volume identity.
It has no infinite-volume value and no `bulk` hypothesis.
-/

namespace YangMills

open MeasureTheory GaugeConfig

variable {d N : ℕ} [NeZero d] [NeZero N]
variable {G : Type*} [Group G] [MeasurableSpace G]

section ConcreteSupport

open Classical in
/-- A positive edge is unchanged by replacing its (already positive) sign by
`true`. -/
private theorem positiveRepresentative_eq (e : PosEdge d N) :
    (⟨{ e.1 with sign := true }, rfl⟩ : PosEdge d N) = e := by
  apply Subtype.ext
  obtain ⟨⟨source, dir, sign⟩, hsign⟩ := e
  simp only at hsign
  subst sign
  rfl

open Classical in
/-- A concrete-edge list enumerating a finite positive-edge support. -/
noncomputable def supportEdgeList (SF : Finset (PosEdge d N)) :
    List (ConcreteEdge d N) :=
  SF.toList.map Subtype.val

open Classical in
@[simp]
theorem edgeSupport_supportEdgeList (SF : Finset (PosEdge d N)) :
    edgeSupport (supportEdgeList SF) = SF := by
  ext e
  constructor
  · intro he
    rw [edgeSupport, List.mem_toFinset, List.mem_map] at he
    obtain ⟨q, hq, hqe⟩ := he
    rw [supportEdgeList, List.mem_map] at hq
    obtain ⟨qpos, hqpos, rfl⟩ := hq
    have hrep := positiveRepresentative_eq qpos
    rw [hrep] at hqe
    simpa [← hqe] using hqpos
  · intro he
    rw [edgeSupport, List.mem_toFinset, List.mem_map]
    refine ⟨e.1, ?_, ?_⟩
    · rw [supportEdgeList, List.mem_map]
      exact ⟨e, by simpa using he, rfl⟩
    · exact positiveRepresentative_eq e

/-- The plaquettes in the selected set whose whole connected component meets
the observable support.  The result can have several connected components. -/
noncomputable def localNear (SF : Finset (PosEdge d N))
    (S : Finset (ConcretePlaquette d N)) :
    Finset (ConcretePlaquette d N) :=
  nearLoop (supportEdgeList SF) S

/-- Plaquettes available to ordinary (unmarked) components once the complete
marked set `S₀` has been selected. -/
noncomputable def localFarRegion (SF : Finset (PosEdge d N))
    (S₀ : Finset (ConcretePlaquette d N)) :
    Finset (ConcretePlaquette d N) :=
  farRegion (supportEdgeList SF) S₀

/-- The finite set of plaquettes meeting the observable support. -/
noncomputable def supportPlaquettes (SF : Finset (PosEdge d N)) :
    Finset (ConcretePlaquette d N) :=
  (localFarRegion SF ∅)ᶜ

open Classical in
/-- The plaquettes excluded from the far gas are exactly those meeting the
combined positive-edge support of the observable and the marked set.  This
is the support identity needed to pin every normalization-cluster remainder
without a volume-cardinality factor. -/
theorem localFarRegion_eq_unionSupport
    (SF : Finset (PosEdge d N))
    (S₀ : Finset (ConcretePlaquette d N)) :
    localFarRegion SF S₀ =
      localFarRegion
        (SF ∪ S₀.biUnion plaquetteSupport) ∅ := by
  ext p
  simp [localFarRegion, farRegion, edgeSupport_supportEdgeList,
    Finset.disjoint_union_left, Finset.disjoint_biUnion_left,
    plaquetteTouches]

open Classical in
/-- Complement form of `localFarRegion_eq_unionSupport`: every plaquette
discarded from the far gas is pinned to the combined local edge support. -/
theorem localFarRegion_compl_eq_supportPlaquettes_union
    (SF : Finset (PosEdge d N))
    (S₀ : Finset (ConcretePlaquette d N)) :
    (localFarRegion SF S₀)ᶜ =
      supportPlaquettes (SF ∪ S₀.biUnion plaquetteSupport) := by
  rw [localFarRegion_eq_unionSupport]
  rfl

/-- A plaquette reads at most four positive-edge coordinates. -/
theorem card_plaquetteSupport_le_four
    (p : ConcretePlaquette d N) :
    (plaquetteSupport p).card ≤ 4 := by
  unfold plaquetteSupport
  refine le_trans (Finset.card_insert_le _ _) ?_
  have h3 : ({(p.edges 1).pos, (p.edges 2).pos, (p.edges 3).pos} :
      Finset (PosEdge d N)).card ≤ 3 := by
    refine le_trans (Finset.card_insert_le _ _) ?_
    have h4 : ({(p.edges 2).pos, (p.edges 3).pos} :
        Finset (PosEdge d N)).card ≤ 2 := by
      refine le_trans (Finset.card_insert_le _ _) ?_
      simp
    omega
  omega

open Classical in
/-- The combined pinning support grows only linearly with the marked
plaquette cardinality. -/
theorem card_union_biUnion_plaquetteSupport_le
    (SF : Finset (PosEdge d N))
    (S₀ : Finset (ConcretePlaquette d N)) :
    (SF ∪ S₀.biUnion plaquetteSupport).card
      ≤ SF.card + 4 * S₀.card := by
  refine (Finset.card_union_le _ _).trans ?_
  simpa [Nat.mul_comm] using
    (Nat.add_le_add_left
      (Finset.card_biUnion_le_card_mul S₀ plaquetteSupport 4
        (fun p _ => card_plaquetteSupport_le_four p))
      SF.card)

open Classical in
theorem localNear_subset (SF : Finset (PosEdge d N))
    (S : Finset (ConcretePlaquette d N)) :
    localNear SF S ⊆ S :=
  nearLoop_subset (supportEdgeList SF) S

open Classical in
theorem card_supportPlaquettes_le (SF : Finset (PosEdge d N)) :
    ((supportPlaquettes SF).card : ℝ)
      ≤ (SF.card : ℝ) * (4 * (d : ℝ)) := by
  have h := card_compl_farRegion_le
    (d := d) (N := N) (supportEdgeList SF)
    (∅ : Finset (ConcretePlaquette d N))
  simpa [supportPlaquettes, localFarRegion] using h

open Classical in
/-- Volume-free incidence count for the complete pinning support of a marked
local term. -/
theorem card_supportPlaquettes_union_le
    (SF : Finset (PosEdge d N))
    (S₀ : Finset (ConcretePlaquette d N)) :
    ((supportPlaquettes
        (SF ∪ S₀.biUnion plaquetteSupport)).card : ℝ)
      ≤ ((SF.card + 4 * S₀.card : ℕ) : ℝ) *
          (4 * (d : ℝ)) := by
  refine (card_supportPlaquettes_le
    (SF ∪ S₀.biUnion plaquetteSupport)).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact_mod_cast card_union_biUnion_plaquetteSupport_le SF S₀

end ConcreteSupport

section GenericTaggedExpansion

open Classical in
/-- Component regrouping for an arbitrary observable carried by the positive
edges `edgeSupport es`.  All components away from that support split off by
product-Haar independence. -/
theorem integral_local_regroup_edges
    (μ : Measure G) [IsProbabilityMeasure μ]
    (F : GaugeConfig d N G → ℂ) (es : List (ConcreteEdge d N))
    (hF : DependsOnPos F (edgeSupport es))
    (f : ConcretePlaquette d N → GaugeConfig d N G → ℂ)
    (hf : ∀ p, DependsOnPos (f p) (plaquetteSupport p))
    (S : Finset (ConcretePlaquette d N)) :
    ∫ A, F A * ∏ p ∈ S, f p A
        ∂(gaugeMeasureFrom (d := d) (N := N) μ)
      = (∫ A, F A * ∏ p ∈ nearLoop es S, f p A
            ∂(gaugeMeasureFrom (d := d) (N := N) μ)) *
        ∫ A, ∏ p ∈ S \ nearLoop es S, f p A
          ∂(gaugeMeasureFrom (d := d) (N := N) μ) := by
  classical
  have hsplit : (fun A : GaugeConfig d N G =>
      F A * ∏ p ∈ S, f p A)
      = fun A => (F A * ∏ p ∈ nearLoop es S, f p A) *
          ∏ p ∈ S \ nearLoop es S, f p A := by
    funext A
    rw [← Finset.prod_sdiff (nearLoop_subset es S)]
    ring
  rw [hsplit]
  refine integral_mul_prod_of_disjoint_support μ (S \ nearLoop es S)
    (fun A => F A * ∏ p ∈ nearLoop es S, f p A) f
    (edgeSupport es ∪ (nearLoop es S).biUnion plaquetteSupport)
    plaquetteSupport ?_ (fun q _ => hf q) ?_
  · refine DependsOnPos.mul (hF.mono Finset.subset_union_left) ?_
    refine DependsOnPos.finset_prod _ _ _ fun p hp => ?_
    exact (hf p).mono
      ((Finset.subset_biUnion_of_mem plaquetteSupport hp).trans
        Finset.subset_union_right)
  · intro q hq
    rw [Finset.mem_sdiff] at hq
    rw [Finset.disjoint_union_left]
    refine ⟨farLoop_disjoint_edgeSupport hq.1 hq.2, ?_⟩
    rw [Finset.disjoint_biUnion_left]
    exact fun p hp => near_far_support_disjoint hp hq.1 hq.2

open Classical in
/-- **Exact marked expansion, edge-list form.**

The numerator is a sum over complete marked plaquette sets `S₀`; the factor
outside the marked integral is the partition function restricted to the
plaquettes disjoint from both the observable support and `S₀`. -/
theorem integral_local_tagged_expansion_edges
    (μ : Measure G) [IsProbabilityMeasure μ]
    (F : GaugeConfig d N G → ℂ) (es : List (ConcreteEdge d N))
    (hF : DependsOnPos F (edgeSupport es))
    (f : ConcretePlaquette d N → GaugeConfig d N G → ℂ)
    (hf : ∀ p, DependsOnPos (f p) (plaquetteSupport p))
    (hint1 : ∀ S : Finset (ConcretePlaquette d N),
      Integrable (fun A => F A * ∏ p ∈ S, f p A)
        (gaugeMeasureFrom (d := d) (N := N) μ))
    (hint2 : ∀ S : Finset (ConcretePlaquette d N),
      Integrable (fun A => ∏ p ∈ S, f p A)
        (gaugeMeasureFrom (d := d) (N := N) μ)) :
    ∫ A, F A * ∏ p : ConcretePlaquette d N, (1 + f p A)
        ∂(gaugeMeasureFrom (d := d) (N := N) μ)
      = ∑ S₀ ∈ (Finset.univ :
            Finset (ConcretePlaquette d N)).powerset.filter
            (fun S₀ => nearLoop es S₀ = S₀),
          (∫ A, F A * ∏ p ∈ S₀, f p A
              ∂(gaugeMeasureFrom (d := d) (N := N) μ)) *
          ∫ A, ∏ p ∈ farRegion es S₀, (1 + f p A)
            ∂(gaugeMeasureFrom (d := d) (N := N) μ) := by
  classical
  have hpt : (fun A : GaugeConfig d N G => F A *
      ∏ p : ConcretePlaquette d N, (1 + f p A))
      = fun A => ∑ S ∈ (Finset.univ :
          Finset (ConcretePlaquette d N)).powerset,
          F A * ∏ p ∈ S, f p A := by
    funext A
    rw [prod_one_add_eq_sum_powerset, Finset.mul_sum]
  rw [hpt, MeasureTheory.integral_finset_sum _ (fun S _ => hint1 S)]
  rw [sum_powerset_fiber es (fun S => ∫ A, F A *
      ∏ p ∈ S, f p A ∂(gaugeMeasureFrom (d := d) (N := N) μ))]
  refine Finset.sum_congr rfl fun S₀ _ => ?_
  have hsplit : ∀ T ∈ (farRegion es S₀).powerset,
      (∫ A, F A * ∏ p ∈ S₀ ∪ T, f p A
          ∂(gaugeMeasureFrom (d := d) (N := N) μ))
        = (∫ A, F A * ∏ p ∈ S₀, f p A
            ∂(gaugeMeasureFrom (d := d) (N := N) μ)) *
          ∫ A, ∏ p ∈ T, f p A
            ∂(gaugeMeasureFrom (d := d) (N := N) μ) := by
    intro T hT
    rw [Finset.mem_powerset] at hT
    have hdisjST : Disjoint S₀ T :=
      (disjoint_farRegion es S₀).mono_right hT
    have hprod : (fun A : GaugeConfig d N G => F A *
        ∏ p ∈ S₀ ∪ T, f p A)
        = fun A => (F A * ∏ p ∈ S₀, f p A) *
            ∏ p ∈ T, f p A := by
      funext A
      rw [Finset.prod_union hdisjST]
      ring
    rw [hprod]
    refine integral_mul_prod_of_disjoint_support μ T
      (fun A => F A * ∏ p ∈ S₀, f p A) f
      (edgeSupport es ∪ S₀.biUnion plaquetteSupport)
      plaquetteSupport ?_ (fun q _ => hf q) ?_
    · refine DependsOnPos.mul (hF.mono Finset.subset_union_left) ?_
      refine DependsOnPos.finset_prod _ _ _ fun p hp => ?_
      exact (hf p).mono
        ((Finset.subset_biUnion_of_mem plaquetteSupport hp).trans
          Finset.subset_union_right)
    · intro q hq
      have hqf := hT hq
      rw [farRegion, Finset.mem_filter] at hqf
      rw [Finset.disjoint_union_left]
      refine ⟨hqf.2.1, ?_⟩
      rw [Finset.disjoint_biUnion_left]
      intro q' hq'
      by_contra hnd
      exact hqf.2.2 q' hq' hnd
  rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum,
    sum_integral_prod_eq_integral_prod_one_add μ f _
      (fun T _ => hint2 T)]

open Classical in
/-- **Exact marked expansion for a finite positive-edge support.**  This is the
support-parametric form used by compatible local observables. -/
theorem integral_localSupport_tagged_expansion
    (μ : Measure G) [IsProbabilityMeasure μ]
    (F : GaugeConfig d N G → ℂ) (SF : Finset (PosEdge d N))
    (hF : DependsOnPos F SF)
    (f : ConcretePlaquette d N → GaugeConfig d N G → ℂ)
    (hf : ∀ p, DependsOnPos (f p) (plaquetteSupport p))
    (hint1 : ∀ S : Finset (ConcretePlaquette d N),
      Integrable (fun A => F A * ∏ p ∈ S, f p A)
        (gaugeMeasureFrom (d := d) (N := N) μ))
    (hint2 : ∀ S : Finset (ConcretePlaquette d N),
      Integrable (fun A => ∏ p ∈ S, f p A)
        (gaugeMeasureFrom (d := d) (N := N) μ)) :
    ∫ A, F A * ∏ p : ConcretePlaquette d N, (1 + f p A)
        ∂(gaugeMeasureFrom (d := d) (N := N) μ)
      = ∑ S₀ ∈ (Finset.univ :
            Finset (ConcretePlaquette d N)).powerset.filter
            (fun S₀ => localNear SF S₀ = S₀),
          (∫ A, F A * ∏ p ∈ S₀, f p A
              ∂(gaugeMeasureFrom (d := d) (N := N) μ)) *
          ∫ A, ∏ p ∈ localFarRegion SF S₀, (1 + f p A)
            ∂(gaugeMeasureFrom (d := d) (N := N) μ) := by
  simpa only [localNear, localFarRegion] using
    integral_local_tagged_expansion_edges μ F (supportEdgeList SF)
      (by simpa using hF) f hf hint1 hint2

end GenericTaggedExpansion

section CompatibleObservableExpansion

variable [MeasurableMul₂ G] [MeasurableInv G]

open Classical in
/-- A Mayer plaquette weight, cast to `ℂ`, reads only the four positive-edge
coordinates in `plaquetteSupport p`. -/
theorem dependsOnPos_plaquetteWeight_ofReal
    (pe : G → ℝ) (β : ℝ) (p : ConcretePlaquette d N) :
    DependsOnPos
      (fun A : GaugeConfig d N G => (plaquetteWeight pe β A p : ℂ))
      (plaquetteSupport p) := by
  intro x y hxy
  apply congrArg (fun r : ℝ => (r : ℂ))
  apply isLocalWeight_plaquetteWeight pe β p
  intro e he
  have hx : configToPos (posToConfig x) = x :=
    (gaugeConfigEquiv (d := d) (N := N) (G := G)).left_inv x
  have hy : configToPos (posToConfig y) = y :=
    (gaugeConfigEquiv (d := d) (N := N) (G := G)).left_inv y
  rw [hx, hy]
  exact hxy e he

open Classical in
/-- Integrability of a bounded compatible local observable times any finite
Mayer monomial. -/
theorem integrable_realize_mul_prod_plaquetteWeight_ofReal
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (O : CompatibleLocalObservable d G) (n : ℕ)
    (S : Finset (ConcretePlaquette d (n + 1))) :
    Integrable (fun A : GaugeConfig d (n + 1) G =>
      (O.realize n A : ℂ) *
        ∏ p ∈ S, (plaquetteWeight pe β A p : ℂ))
      (gaugeMeasureFrom (d := d) (N := n + 1) μ) := by
  have hprodR := integrable_prod_plaquetteWeight
    (d := d) (N := n + 1) μ hpe_meas hpe β S
  have hprodC : Integrable (fun A : GaugeConfig d (n + 1) G =>
      ∏ p ∈ S, (plaquetteWeight pe β A p : ℂ))
      (gaugeMeasureFrom (d := d) (N := n + 1) μ) := by
    convert hprodR.ofReal (𝕜 := ℂ) using 1
    funext A
    push_cast
    rfl
  have hOmeas : Measurable
      (fun A : GaugeConfig d (n + 1) G => (O.realize n A : ℂ)) := by
    exact (O.measurable_realize n).complex_ofReal
  have hmul := hprodC.bdd_mul hOmeas.aestronglyMeasurable
    (ae_of_all _ fun A => by
      simpa [Complex.norm_real, Real.norm_eq_abs] using O.abs_realize_le n A)
  simpa [mul_comm] using hmul

open Classical in
/-- Integrability of a finite complex-cast Mayer monomial. -/
theorem integrable_prod_plaquetteWeight_ofReal
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (S : Finset (ConcretePlaquette d N)) :
    Integrable (fun A : GaugeConfig d N G =>
      ∏ p ∈ S, (plaquetteWeight pe β A p : ℂ))
      (gaugeMeasureFrom (d := d) (N := N) μ) := by
  have hR := integrable_prod_plaquetteWeight
    (d := d) (N := N) μ hpe_meas hpe β S
  convert hR.ofReal (𝕜 := ℂ) using 1
  funext A
  push_cast
  rfl

/-- The unnormalized complex numerator used by the marked expansion. -/
noncomputable def localGibbsNumerator
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G) (n : ℕ) : ℂ :=
  ∫ A, (O.realize n A : ℂ) *
      ∏ p : ConcretePlaquette d (n + 1),
        ((1 : ℂ) + (plaquetteWeight pe β A p : ℂ))
    ∂(gaugeMeasureFrom (d := d) (N := n + 1) μ)

open Classical in
/-- **Exact marked numerator identity for a compatible local observable.**

Every connected component of the marked set meets the realized support, but
the marked set itself is deliberately allowed to be disconnected. -/
theorem localGibbsNumerator_eq_markedSum
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (O : CompatibleLocalObservable d G) (n : ℕ)
    (hvol : O.minVolume ≤ n) :
    localGibbsNumerator μ pe β O n
      = ∑ S₀ ∈ (Finset.univ :
            Finset (ConcretePlaquette d (n + 1))).powerset.filter
            (fun S₀ => localNear (O.realizedSupport n hvol) S₀ = S₀),
          (∫ A, (O.realize n A : ℂ) *
              ∏ p ∈ S₀, (plaquetteWeight pe β A p : ℂ)
              ∂(gaugeMeasureFrom (d := d) (N := n + 1) μ)) *
          ∫ A, ∏ p ∈ localFarRegion (O.realizedSupport n hvol) S₀,
              ((1 : ℂ) + (plaquetteWeight pe β A p : ℂ))
            ∂(gaugeMeasureFrom (d := d) (N := n + 1) μ) := by
  unfold localGibbsNumerator
  exact integral_localSupport_tagged_expansion μ
    (fun A : GaugeConfig d (n + 1) G => (O.realize n A : ℂ))
    (O.realizedSupport n hvol) (O.dependsOnPos_realize n hvol)
    (fun p A => (plaquetteWeight pe β A p : ℂ))
    (dependsOnPos_plaquetteWeight_ofReal pe β)
    (fun S => integrable_realize_mul_prod_plaquetteWeight_ofReal
      μ hpe_meas hpe β O n S)
    (fun S => integrable_prod_plaquetteWeight_ofReal
      μ hpe_meas hpe β S)

/-- Gibbs expectation as its genuine unnormalized Boltzmann integral divided
by the genuine partition function.  This is finite-volume measure calculus,
not a cluster-expansion assumption. -/
theorem localGibbsExpectation_eq_boltzmann_div
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G) (n : ℕ) :
    localGibbsExpectation μ pe β O n
      = (∫ A, O.realize n A *
            Real.exp (-β * wilsonAction pe A)
          ∂(gaugeMeasureFrom (d := d) (N := n + 1) μ)) /
        partitionFunction (d := d) (N := n + 1) μ pe β := by
  unfold localGibbsExpectation expectation gibbsMeasure partitionFunction
  rw [MeasureTheory.integral_tilted]
  rw [← MeasureTheory.integral_div]
  congr 1
  funext A
  dsimp only
  rw [smul_eq_mul]
  ring

open Classical in
/-- The genuine Gibbs expectation is exactly the marked numerator divided by
the genuine weighted partition function. -/
theorem localGibbsExpectation_eq_numerator_div
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G) (n : ℕ) :
    (localGibbsExpectation μ pe β O n : ℂ)
      = localGibbsNumerator μ pe β O n /
          (weightedPartition (d := d) (N := n + 1) μ
            (fun A p => plaquetteWeight pe β A p) : ℂ) := by
  rw [localGibbsExpectation_eq_boltzmann_div]
  rw [Complex.ofReal_div, weightedPartition_plaquetteWeight]
  congr 1
  unfold localGibbsNumerator
  rw [← integral_complex_ofReal]
  congr 1
  funext A
  push_cast
  congr 1
  have h := congrArg (fun r : ℝ => (r : ℂ))
    (prod_one_add_plaquetteWeight (d := d) pe β A)
  push_cast at h
  exact h.symm

open Classical in
/-- **The missing one-volume bridge:** the genuine local Gibbs expectation is
the exact marked sum, normalized by the exact finite-volume partition
function.  No free infinite-volume value appears. -/
theorem localGibbsExpectation_eq_markedSum_div
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (O : CompatibleLocalObservable d G) (n : ℕ)
    (hvol : O.minVolume ≤ n) :
    (localGibbsExpectation μ pe β O n : ℂ)
      = (∑ S₀ ∈ (Finset.univ :
            Finset (ConcretePlaquette d (n + 1))).powerset.filter
            (fun S₀ => localNear (O.realizedSupport n hvol) S₀ = S₀),
          (∫ A, (O.realize n A : ℂ) *
              ∏ p ∈ S₀, (plaquetteWeight pe β A p : ℂ)
              ∂(gaugeMeasureFrom (d := d) (N := n + 1) μ)) *
          ∫ A, ∏ p ∈ localFarRegion (O.realizedSupport n hvol) S₀,
              ((1 : ℂ) + (plaquetteWeight pe β A p : ℂ))
            ∂(gaugeMeasureFrom (d := d) (N := n + 1) μ)) /
        (weightedPartition (d := d) (N := n + 1) μ
          (fun A p => plaquetteWeight pe β A p) : ℂ) := by
  rw [localGibbsExpectation_eq_numerator_div,
    localGibbsNumerator_eq_markedSum μ hpe_meas hpe β O n hvol]

open Classical in
/-- Exact cancellation of a region-restricted partition function against the
full partition function, expressed as a cluster-sum difference. -/
theorem restrictedWeightedPartition_div_eq_exp_clusterDiff
    (μ : Measure G) [IsProbabilityMeasure μ]
    {w : GaugeConfig d N G → ConcretePlaquette d N → ℝ}
    (hloc : IsLocalWeight (d := d) (N := N) (G := G) w)
    (hmeas : ∀ p : ConcretePlaquette d N,
      Measurable (fun A : GaugeConfig d N G => w A p))
    {δ : ℝ} (hbd : ∀ A p, |w A p| ≤ δ)
    {a : (weightedLatticePolymerSystem (d := d) (N := N) μ w).Polymer → ℝ}
    (hkp : KP.KPCriterion
      (weightedLatticePolymerSystem (d := d) (N := N) μ w) a)
    (F : Finset (ConcretePlaquette d N)) :
    (∫ A, ∏ p ∈ F, ((1 : ℂ) + (w A p : ℂ))
        ∂(gaugeMeasureFrom (d := d) (N := N) μ)) /
        (weightedPartition (d := d) (N := N) μ w : ℂ)
      = Complex.exp (
          KP.clusterSum
            ((weightedLatticePolymerSystem (d := d) (N := N) μ w).restrict
              (Finset.univ.filter (fun c => c.1 ⊆ F)))
          - KP.clusterSum
            (weightedLatticePolymerSystem (d := d) (N := N) μ w)) := by
  let P := weightedLatticePolymerSystem (d := d) (N := N) μ w
  let Λ : Finset P.Polymer := Finset.univ.filter (fun c => c.1 ⊆ F)
  have hnum :
      ∫ A, ∏ p ∈ F, ((1 : ℂ) + (w A p : ℂ))
          ∂(gaugeMeasureFrom (d := d) (N := N) μ)
        = Complex.exp (KP.clusterSum (P.restrict Λ)) := by
    calc
      (∫ A, ∏ p ∈ F, ((1 : ℂ) + (w A p : ℂ))
          ∂(gaugeMeasureFrom (d := d) (N := N) μ))
          = ((∫ A, ∏ p ∈ F, (1 + w A p)
              ∂(gaugeMeasureFrom (d := d) (N := N) μ) : ℝ) : ℂ) :=
            integral_prod_one_add_ofReal μ w F
      _ = KP.partition P Λ :=
            restricted_weightedPartition_eq_partition μ hloc hmeas hbd F
      _ = Complex.exp (KP.clusterSum (P.restrict Λ)) :=
            KP.partition_eq_exp_clusterSum_restrict hkp Λ
  have hden :
      (weightedPartition (d := d) (N := N) μ w : ℂ)
        = Complex.exp (KP.clusterSum P) := by
    calc
      (weightedPartition (d := d) (N := N) μ w : ℂ)
          = KP.partition P Finset.univ :=
            weightedPartition_eq_partition μ hloc hmeas hbd
      _ = Complex.exp (KP.clusterSum P) :=
            KP.partition_eq_exp_clusterSum_of_kp P hkp
  rw [hnum, hden]
  exact (Complex.exp_sub _ _).symm

open Classical in
/-- **Exact one-volume marked cluster formula.**  The ordinary gas has
cancelled completely.  What remains is a finite sum of marked integrals times
cluster differences pinned to the marked support. -/
theorem localGibbsExpectation_eq_markedClusterSum
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (O : CompatibleLocalObservable d G) (n : ℕ)
    (hvol : O.minVolume ≤ n)
    {a : (weightedLatticePolymerSystem (d := d) (N := n + 1) μ
      (fun A p => plaquetteWeight pe β A p)).Polymer → ℝ}
    (hkp : KP.KPCriterion
      (weightedLatticePolymerSystem (d := d) (N := n + 1) μ
        (fun A p => plaquetteWeight pe β A p)) a) :
    (localGibbsExpectation μ pe β O n : ℂ)
      = ∑ S₀ ∈ (Finset.univ :
            Finset (ConcretePlaquette d (n + 1))).powerset.filter
            (fun S₀ => localNear (O.realizedSupport n hvol) S₀ = S₀),
          (∫ A, (O.realize n A : ℂ) *
              ∏ p ∈ S₀, (plaquetteWeight pe β A p : ℂ)
              ∂(gaugeMeasureFrom (d := d) (N := n + 1) μ)) *
          Complex.exp (
            KP.clusterSum
              ((weightedLatticePolymerSystem (d := d) (N := n + 1) μ
                (fun A p => plaquetteWeight pe β A p)).restrict
                (Finset.univ.filter (fun c =>
                  c.1 ⊆ localFarRegion (O.realizedSupport n hvol) S₀)))
            - KP.clusterSum
              (weightedLatticePolymerSystem (d := d) (N := n + 1) μ
                (fun A p => plaquetteWeight pe β A p))) := by
  have hδ : ∀ (A : GaugeConfig d (n + 1) G)
      (p : ConcretePlaquette d (n + 1)),
      |plaquetteWeight pe β A p| ≤ Real.exp (|β| * B) - 1 :=
    fun A p => abs_plaquetteWeight_le pe β A p hpe
  have hmeas : ∀ p : ConcretePlaquette d (n + 1),
      Measurable (fun A : GaugeConfig d (n + 1) G =>
        plaquetteWeight pe β A p) := by
    intro p
    unfold plaquetteWeight
    exact (Real.measurable_exp.comp
      ((hpe_meas.comp (measurable_plaquetteHolonomy p)).const_mul
        (-β))).sub measurable_const
  rw [localGibbsExpectation_eq_markedSum_div μ hpe_meas hpe β O n hvol,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun S₀ hS₀ => ?_
  rw [mul_div_assoc]
  congr 1
  exact restrictedWeightedPartition_div_eq_exp_clusterDiff μ
    (isLocalWeight_plaquetteWeight pe β) hmeas hδ hkp
    (localFarRegion (O.realizedSupport n hvol) S₀)

end CompatibleObservableExpansion

section SupportPinnedRemainder

variable [MeasurableMul₂ G] [MeasurableInv G]

open Classical in
/-- The singleton connected polymer rooted at a plaquette. -/
noncomputable def singletonConnectedPolymer
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (p : ConcretePlaquette d N) :
    (connectedLatticePolymerSystem (d := d) (N := N) μ pe β).Polymer :=
  ⟨{p}, Finset.singleton_nonempty p, SimpleGraph.Connected.of_subsingleton⟩

open Classical in
/-- Pinned cluster tails rooted at every plaquette meeting a finite
positive-edge support.  This is the boundary term appropriate to an arbitrary
local observable; it has no volume-cardinality factor. -/
noncomputable def supportPinnedBoundaryRemainder
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (SF : Finset (PosEdge d N)) (L K : ℕ) : ℝ :=
  ∑ p ∈ supportPlaquettes SF,
    pinnedBoundaryRemainder μ pe β
      (singletonConnectedPolymer μ pe β p) L K

open Classical in
/-- **Uniform boundary estimate for an arbitrary finite edge support.**

`connectedLattice_pinned_tail_volumeUniform` enters through
`pinnedBoundaryRemainder_le_volumeUniform`; the only prefactor is the number
of support edges times the local `4d` incidence bound. -/
theorem supportPinnedBoundaryRemainder_le_volumeUniform
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (t ε : ℝ) (ht0 : 0 ≤ t) (hε0 : 0 ≤ ε)
    (hr : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      ((Real.exp (|β| * B) - 1) * Real.exp (t + ε)) < 1)
    (hsmall : ((16 * d : ℕ) : ℝ) *
      (((Real.exp (|β| * B) - 1) * Real.exp (t + ε)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          ((Real.exp (|β| * B) - 1) * Real.exp (t + ε)))) ≤ t)
    (SF : Finset (PosEdge d N)) (L K : ℕ) :
    supportPinnedBoundaryRemainder μ pe β SF L K
      ≤ Real.exp (-(ε * L)) *
          (t * ((SF.card : ℝ) * (4 * (d : ℝ)))) := by
  classical
  unfold supportPinnedBoundaryRemainder
  calc
    (∑ p ∈ supportPlaquettes SF,
        pinnedBoundaryRemainder μ pe β
          (singletonConnectedPolymer μ pe β p) L K)
        ≤ ∑ _p ∈ supportPlaquettes SF,
            Real.exp (-(ε * L)) * t := by
          refine Finset.sum_le_sum fun p _ => ?_
          simpa [singletonConnectedPolymer] using
            pinnedBoundaryRemainder_le_volumeUniform
              μ hpe β t ε ht0 hε0 hr hsmall
              (singletonConnectedPolymer μ pe β p) L K
    _ = ((supportPlaquettes SF).card : ℝ) *
          (Real.exp (-(ε * L)) * t) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((SF.card : ℝ) * (4 * (d : ℝ))) *
          (Real.exp (-(ε * L)) * t) := by
          exact mul_le_mul_of_nonneg_right
            (card_supportPlaquettes_le SF)
            (mul_nonneg (Real.exp_pos _).le ht0)
    _ = Real.exp (-(ε * L)) *
          (t * ((SF.card : ℝ) * (4 * (d : ℝ)))) := by ring

end SupportPinnedRemainder

end YangMills
