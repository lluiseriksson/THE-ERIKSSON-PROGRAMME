/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.L1_GibbsMeasure.EdgeFactorization
import YangMills.L1_GibbsMeasure.CenterInvariance
import YangMills.L1_GibbsMeasure.PolymerExpansion
import YangMills.L1_GibbsMeasure.ClusterGeometry
import YangMills.ClayCore.WilsonLine
import YangMills.L0_Lattice.ChainComplex

/-!
# Support-disjoint factorization over the gauge measure (VU campaign, V0)

`docs/AREA-LAW-VU-PLAN.md` V0: the β = 0 gauge measure is the product
of per-positive-edge Haar coordinates, so observables with **disjoint
positive-edge supports are independent** — the factorization that lets
polymer components disjoint from a Wilson loop's support split off the
loop-tagged expansion (the first step of the connected-support
resummation against `Z`).

* `DependsOnPos F S` — `F` reads only the positive-edge coordinates
  in `S`;
* `edgeSupport es` / `plaquetteSupport p` — the positive-edge support
  of a Wilson list / of a plaquette;
* `dependsOnPos_comp_wilsonLine` — `φ(W_es)` depends only on
  `edgeSupport es` (covers traces, linearized AND exponential
  activities uniformly, via the post-composition `φ`);
* `integral_mul_of_disjoint_pos_deps` — the two-block independence
  `∫ F·K = ∫F · ∫K` over `gaugeMeasureFrom μ`;
* `integral_mul_prod_of_disjoint_support` — **V0 headline**: an
  observable times a product of activities whose supports avoid the
  observable's support factorizes;
* `integral_wilson_obs_mul_prod_split` — the Wilson-loop
  instantiation.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills

open MeasureTheory GaugeConfig

variable {d N : ℕ} [NeZero d] [NeZero N] {G : Type*} [Group G] [MeasurableSpace G]

/-! ## Dependence on a set of positive-edge coordinates -/

/-- `F` depends only on the positive-edge coordinates in `S`: its value
on the gauge field built from coordinates `x` is unchanged when `x` is
modified outside `S`. -/
def DependsOnPos (F : GaugeConfig d N G → ℂ) (S : Finset (PosEdge d N)) : Prop :=
  ∀ x y : PosEdge d N → G, (∀ pe ∈ S, x pe = y pe) →
    F (posToConfig x) = F (posToConfig y)

theorem DependsOnPos.mono {F : GaugeConfig d N G → ℂ}
    {S T : Finset (PosEdge d N)} (hST : S ⊆ T)
    (hF : DependsOnPos F S) : DependsOnPos F T :=
  fun x y h => hF x y fun pe hpe => h pe (hST hpe)

theorem DependsOnPos.mul {F K : GaugeConfig d N G → ℂ}
    {S : Finset (PosEdge d N)}
    (hF : DependsOnPos F S) (hK : DependsOnPos K S) :
    DependsOnPos (fun A => F A * K A) S := fun x y h => by
  show F (posToConfig x) * K (posToConfig x)
      = F (posToConfig y) * K (posToConfig y)
  rw [hF x y h, hK x y h]

theorem DependsOnPos.finset_prod {ι : Type*} (s : Finset ι)
    (g : ι → GaugeConfig d N G → ℂ) (S : Finset (PosEdge d N))
    (hg : ∀ i ∈ s, DependsOnPos (g i) S) :
    DependsOnPos (fun A => ∏ i ∈ s, g i A) S := fun x y h =>
  Finset.prod_congr rfl fun i hi => hg i hi x y h

/-! ## Edge supports -/

open Classical in
/-- The **positive-edge support** of a Wilson list: the set of Haar
coordinates its holonomy reads. -/
noncomputable def edgeSupport (es : List (ConcreteEdge d N)) :
    Finset (PosEdge d N) :=
  (es.map fun e => (⟨{ e with sign := true }, rfl⟩ : PosEdge d N)).toFinset

open Classical in
theorem mem_edgeSupport_of_mem {es : List (ConcreteEdge d N)}
    {e : ConcreteEdge d N} (he : e ∈ es) :
    (⟨{ e with sign := true }, rfl⟩ : PosEdge d N) ∈ edgeSupport es := by
  unfold edgeSupport
  rw [List.mem_toFinset]
  exact List.mem_map.mpr ⟨e, he, rfl⟩

/-- The **positive-edge support of a plaquette**: the coordinates its
holonomy trace (and hence any plaquette activity) reads.  (Named to
avoid clashing with `plaquetteSupport : Finset (ConcreteEdge d N)` of
`PolymerExpansion`, which lives at the signed-edge level.) -/
noncomputable def plaquettePosSupport
    (p : FiniteLatticeGeometry.P (d := d) (N := N) (G := G)) :
    Finset (PosEdge d N) :=
  edgeSupport (plaquetteList (d := d) (N := N) (G := G) p)

/-! ## Dependence of Wilson observables on their support -/

/-- Evaluating the gauge field built from coordinates `x` on a concrete
edge reads only the coordinate at the edge's positive representative. -/
theorem posToFun_congr_at (x y : PosEdge d N → G) (e : ConcreteEdge d N)
    (h : x ⟨{ e with sign := true }, rfl⟩ = y ⟨{ e with sign := true }, rfl⟩) :
    posToFun x e = posToFun y e := by
  obtain ⟨src, dir, sign⟩ := e
  unfold posToFun
  cases sign
  · rw [dif_neg (by simp), dif_neg (by simp)]
    exact congrArg Inv.inv h
  · rw [dif_pos rfl, dif_pos rfl]
    exact h

/-- Wilson lines are insensitive to coordinate changes outside their
edge list. -/
theorem wilsonLine_posToConfig_congr (x y : PosEdge d N → G)
    (es : List (ConcreteEdge d N))
    (h : ∀ e ∈ es,
      x ⟨{ e with sign := true }, rfl⟩ = y ⟨{ e with sign := true }, rfl⟩) :
    wilsonLine (posToConfig x) es = wilsonLine (posToConfig y) es := by
  induction es with
  | nil => rfl
  | cons e tl ih =>
      rw [wilsonLine_cons, wilsonLine_cons]
      have h1 : posToConfig x e = posToConfig y e :=
        posToFun_congr_at x y e (h e List.mem_cons_self)
      rw [h1, ih fun e' he' => h e' (List.mem_cons_of_mem _ he')]

/-- **Any post-composed Wilson-line observable depends only on the
line's edge support.**  Instantiations: the loop trace
(`φ = fun U => Matrix.trace U.val`), the linearized activity
(`φ = fun U => c·tr U + c'·conj tr U`), and the exact Wilson activity
(`φ = fun U => exp(c·tr U + c'·conj tr U)`). -/
theorem dependsOnPos_comp_wilsonLine (φ : G → ℂ)
    (es : List (ConcreteEdge d N)) :
    DependsOnPos (fun A => φ (wilsonLine A es)) (edgeSupport es) := by
  intro x y h
  have hW : wilsonLine (posToConfig x) es = wilsonLine (posToConfig y) es :=
    wilsonLine_posToConfig_congr x y es fun e he =>
      h _ (mem_edgeSupport_of_mem he)
  show φ (wilsonLine (posToConfig x) es) = φ (wilsonLine (posToConfig y) es)
  rw [hW]

/-- Plaquette observables depend only on the plaquette's support. -/
theorem dependsOnPos_plaquette_obs (φ : G → ℂ)
    (p : FiniteLatticeGeometry.P (d := d) (N := N) (G := G)) :
    DependsOnPos
      (fun A => φ (wilsonLine A (plaquetteList (d := d) (N := N) (G := G) p)))
      (plaquettePosSupport p) :=
  dependsOnPos_comp_wilsonLine φ _

/-- **The support bridge (V0-2 opening):** the positive-edge support of
a plaquette's Wilson list coincides with the polymer layer's
`plaquetteSupport` (the four `.pos` coordinates) — so `ClusterGeometry`'s
component/touching combinatorics and V0-1's independence speak about
the SAME `Finset (PosEdge d N)`. -/
theorem plaquettePosSupport_eq (p : ConcretePlaquette d N) :
    plaquettePosSupport (d := d) (N := N) (G := G) p = plaquetteSupport p := by
  classical
  ext pe
  simp only [plaquettePosSupport, edgeSupport, plaquetteList, plaquetteSupport,
    ConcreteEdge.pos, List.mem_toFinset, List.mem_map, List.mem_cons,
    List.mem_singleton, List.not_mem_nil, or_false, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨e, (rfl | rfl | rfl | rfl), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨_, Or.inl rfl, rfl⟩
    · exact ⟨_, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inr rfl)), rfl⟩

/-- Plaquette observables depend only on the polymer layer's
`plaquetteSupport` — the form the component regrouping consumes. -/
theorem dependsOnPos_plaquette_obs' (φ : G → ℂ)
    (p : ConcretePlaquette d N) :
    DependsOnPos
      (fun A => φ (wilsonLine A (plaquetteList (d := d) (N := N) (G := G) p)))
      (plaquetteSupport p) :=
  plaquettePosSupport_eq (G := G) p ▸ dependsOnPos_plaquette_obs φ p

/-! ## The factorization theorems -/

/-- **Two-block independence over the gauge measure:** observables
reading disjoint blocks of positive-edge coordinates have factorizing
expectations.  This is `integral_mul_of_disjoint_deps_complex`
transported along `gaugeConfigMEquiv`. -/
theorem integral_mul_of_disjoint_pos_deps
    (μ : Measure G) [IsProbabilityMeasure μ]
    (S : Finset (PosEdge d N)) (F K : GaugeConfig d N G → ℂ)
    (hF : DependsOnPos F S) (hK : DependsOnPos K Sᶜ) :
    ∫ A, F A * K A ∂(gaugeMeasureFrom (d := d) (N := N) μ)
      = (∫ A, F A ∂(gaugeMeasureFrom (d := d) (N := N) μ)) *
        ∫ A, K A ∂(gaugeMeasureFrom (d := d) (N := N) μ) := by
  classical
  have hmeas : gaugeMeasureFrom (d := d) (N := N) μ
      = Measure.map (gaugeConfigMEquiv (d := d) (N := N) (G := G))
          (Measure.pi (fun _ : PosEdge d N => μ)) := rfl
  rw [hmeas, MeasureTheory.integral_map_equiv,
    MeasureTheory.integral_map_equiv, MeasureTheory.integral_map_equiv]
  exact integral_mul_of_disjoint_deps_complex μ (fun pe => pe ∈ S)
    (fun x => F (posToConfig x)) (fun x => K (posToConfig x))
    (fun x y hxy => hF x y hxy)
    (fun x y hxy => hK x y fun pe hpe => hxy pe (Finset.mem_compl.mp hpe))

/-- **V0 headline — support-disjoint activities split off:** an
observable `F` supported on `SF` times a product of activities whose
supports all avoid `SF` factorizes over the gauge measure.  This is
the mechanism by which polymer components disjoint from the Wilson
loop's support will cancel against `Z` in the connected-support
resummation. -/
theorem integral_mul_prod_of_disjoint_support
    (μ : Measure G) [IsProbabilityMeasure μ] {ι : Type*}
    (s : Finset ι) (F : GaugeConfig d N G → ℂ)
    (g : ι → GaugeConfig d N G → ℂ)
    (SF : Finset (PosEdge d N)) (Sg : ι → Finset (PosEdge d N))
    (hF : DependsOnPos F SF) (hg : ∀ i ∈ s, DependsOnPos (g i) (Sg i))
    (hdisj : ∀ i ∈ s, Disjoint SF (Sg i)) :
    ∫ A, F A * ∏ i ∈ s, g i A ∂(gaugeMeasureFrom (d := d) (N := N) μ)
      = (∫ A, F A ∂(gaugeMeasureFrom (d := d) (N := N) μ)) *
        ∫ A, ∏ i ∈ s, g i A ∂(gaugeMeasureFrom (d := d) (N := N) μ) := by
  classical
  refine integral_mul_of_disjoint_pos_deps μ SF F
    (fun A => ∏ i ∈ s, g i A) hF ?_
  refine DependsOnPos.finset_prod s g SFᶜ ?_
  intro i hi
  refine (hg i hi).mono ?_
  intro pe hpe
  rw [Finset.mem_compl]
  exact fun hmem => (Finset.disjoint_left.mp (hdisj i hi)) hmem hpe

/-! ## V0-2: the component regrouping

Split a plaquette set's activities by whether their touching component
(`plaqComponents`, banked in `ClusterGeometry`) meets the loop's edge
support; the far components factor out of the loop integral. -/

open Classical in
/-- The plaquettes of `S` whose touching component meets the loop's
support — the part of a powerset term that stays coupled to `W_C`. -/
noncomputable def nearLoop (es : List (ConcreteEdge d N))
    (S : Finset (ConcretePlaquette d N)) :
    Finset (ConcretePlaquette d N) :=
  ((plaqComponents S).filter
    (fun c => ∃ p ∈ c,
      ¬ Disjoint (edgeSupport (d := d) (N := N) es) (plaquetteSupport p))).biUnion id

open Classical in
theorem nearLoop_subset (es : List (ConcreteEdge d N))
    (S : Finset (ConcretePlaquette d N)) : nearLoop es S ⊆ S := by
  intro p hp
  rw [nearLoop, Finset.mem_biUnion] at hp
  obtain ⟨c, hc, hpc⟩ := hp
  exact plaqComponents_subset (Finset.mem_filter.mp hc).1 hpc

open Classical in
/-- Every plaquette of `S` lies in some touching component. -/
theorem mem_plaqComponents_of_mem {S : Finset (ConcretePlaquette d N)}
    {q : ConcretePlaquette d N} (hq : q ∈ S) :
    ∃ c ∈ plaqComponents S, q ∈ c := by
  rw [← plaqComponents_biUnion S, Finset.mem_biUnion] at hq
  obtain ⟨c, hc, hqc⟩ := hq
  exact ⟨c, hc, hqc⟩

open Classical in
/-- A plaquette outside `nearLoop` has support disjoint from the
loop's. -/
theorem farLoop_disjoint_edgeSupport {es : List (ConcreteEdge d N)}
    {S : Finset (ConcretePlaquette d N)} {q : ConcretePlaquette d N}
    (hq : q ∈ S) (hnear : q ∉ nearLoop es S) :
    Disjoint (edgeSupport (d := d) (N := N) es) (plaquetteSupport q) := by
  obtain ⟨c, hc, hqc⟩ := mem_plaqComponents_of_mem hq
  by_contra hnd
  exact hnear (Finset.mem_biUnion.mpr
    ⟨c, Finset.mem_filter.mpr ⟨hc, ⟨q, hqc, hnd⟩⟩, hqc⟩)

open Classical in
/-- Near and far plaquettes have disjoint supports: they lie in
DIFFERENT touching components, and distinct components are
support-disjoint. -/
theorem near_far_support_disjoint {es : List (ConcreteEdge d N)}
    {S : Finset (ConcretePlaquette d N)} {p q : ConcretePlaquette d N}
    (hp : p ∈ nearLoop es S) (hq : q ∈ S) (hqf : q ∉ nearLoop es S) :
    Disjoint (plaquetteSupport p) (plaquetteSupport q) := by
  rw [nearLoop, Finset.mem_biUnion] at hp
  obtain ⟨cp, hcp, hpcp⟩ := hp
  rw [Finset.mem_filter] at hcp
  obtain ⟨cq, hcq, hqcq⟩ := mem_plaqComponents_of_mem hq
  have hne : cp ≠ cq := by
    rintro rfl
    exact hqf (Finset.mem_biUnion.mpr
      ⟨cp, Finset.mem_filter.mpr hcp, hqcq⟩)
  exact (plaqComponents_support_disjoint hcp.1 hcq hne).mono
    (Finset.subset_biUnion_of_mem plaquetteSupport hpcp)
    (Finset.subset_biUnion_of_mem plaquetteSupport hqcq)

open Classical in
/-- **V0-2 — the component regrouping:** in any powerset term of the
loop-tagged expansion, the activities of the components NOT touching
the loop split off as an independent factor:

`∫ φ(W_C)·∏_{p∈S} f_p = (∫ φ(W_C)·∏_{near} f_p) · (∫ ∏_{far} f_p)`. -/
theorem integral_wilson_obs_regroup
    (μ : Measure G) [IsProbabilityMeasure μ]
    (φ : G → ℂ) (es : List (ConcreteEdge d N))
    (f : ConcretePlaquette d N → GaugeConfig d N G → ℂ)
    (hf : ∀ p, DependsOnPos (f p) (plaquetteSupport p))
    (S : Finset (ConcretePlaquette d N)) :
    ∫ A, φ (wilsonLine A es) * ∏ p ∈ S, f p A
        ∂(gaugeMeasureFrom (d := d) (N := N) μ)
      = (∫ A, φ (wilsonLine A es) * ∏ p ∈ nearLoop es S, f p A
            ∂(gaugeMeasureFrom (d := d) (N := N) μ)) *
        ∫ A, ∏ p ∈ S \ nearLoop es S, f p A
          ∂(gaugeMeasureFrom (d := d) (N := N) μ) := by
  classical
  have hsplit : (fun A : GaugeConfig d N G =>
      φ (wilsonLine A es) * ∏ p ∈ S, f p A)
      = fun A => (φ (wilsonLine A es) * ∏ p ∈ nearLoop es S, f p A) *
          ∏ p ∈ S \ nearLoop es S, f p A := by
    funext A
    rw [← Finset.prod_sdiff (nearLoop_subset es S)]
    ring
  rw [hsplit]
  refine integral_mul_prod_of_disjoint_support μ (S \ nearLoop es S)
    (fun A => φ (wilsonLine A es) * ∏ p ∈ nearLoop es S, f p A) f
    (edgeSupport (d := d) (N := N) es ∪
      (nearLoop es S).biUnion plaquetteSupport)
    plaquetteSupport ?_ (fun q _ => hf q) ?_
  · refine DependsOnPos.mul ?_ ?_
    · exact (dependsOnPos_comp_wilsonLine φ es).mono
        Finset.subset_union_left
    · refine DependsOnPos.finset_prod _ _ _ fun p hp => ?_
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
/-- The **far region** of a pinned set `S₀`: the plaquettes whose
support avoids both the loop and `S₀` — the index set the far subsets
`T` of the fiber decomposition `S = S₀ ⊎ T` range over. -/
noncomputable def farRegion (es : List (ConcreteEdge d N))
    (S₀ : Finset (ConcretePlaquette d N)) :
    Finset (ConcretePlaquette d N) :=
  Finset.univ.filter (fun p =>
    Disjoint (edgeSupport (d := d) (N := N) es) (plaquetteSupport p) ∧
    ∀ q ∈ S₀, ¬ plaquetteTouches q p)

open Classical in
/-- The forward half of the V1-b fiber map: the far part of any `S`
lies in the far region of its near part. -/
theorem sdiff_nearLoop_subset_farRegion (es : List (ConcreteEdge d N))
    (S : Finset (ConcretePlaquette d N)) :
    S \ nearLoop es S ⊆ farRegion es (nearLoop es S) := by
  intro p hp
  rw [Finset.mem_sdiff] at hp
  rw [farRegion, Finset.mem_filter]
  refine ⟨Finset.mem_univ _,
    farLoop_disjoint_edgeSupport hp.1 hp.2, fun q hq htouch => ?_⟩
  exact htouch (near_far_support_disjoint hq hp.1 hp.2)

open Classical in
/-- **Membership in `nearLoop` is reachability to a loop-touching
plaquette** in the internal touching graph — the characterization that
makes `nearLoop` stable under far unions (V1-b). -/
theorem mem_nearLoop_iff_reachable {es : List (ConcreteEdge d N)}
    {S : Finset (ConcretePlaquette d N)} {p : ConcretePlaquette d N}
    (hp : p ∈ S) :
    p ∈ nearLoop es S ↔ ∃ q : ↥S,
      (SimpleGraph.fromRel (fun a b : ↥S =>
        plaquetteTouches a.1 b.1)).Reachable ⟨p, hp⟩ q ∧
      ¬ Disjoint (edgeSupport (d := d) (N := N) es)
        (plaquetteSupport q.1) := by
  classical
  constructor
  · intro hmem
    rw [nearLoop, Finset.mem_biUnion] at hmem
    obtain ⟨c, hc, hpc⟩ := hmem
    rw [Finset.mem_filter] at hc
    obtain ⟨hcparts, q', hq'c, hq'⟩ := hc
    unfold plaqComponents at hcparts
    rw [Finset.mem_image] at hcparts
    obtain ⟨B, hB, rfl⟩ := hcparts
    simp only [id_eq] at hpc
    rw [Finset.mem_image] at hpc hq'c
    obtain ⟨x, hxB, hxp⟩ := hpc
    obtain ⟨y, hyB, hyq⟩ := hq'c
    have h1 := (Finpartition.ofSetoid _).part_eq_of_mem hB hxB
    have hyPx : y ∈ (Finpartition.ofSetoid
        ((SimpleGraph.fromRel (fun a b : ↥S =>
          plaquetteTouches a.1 b.1)).reachableSetoid)).part x := h1 ▸ hyB
    have hreach : (SimpleGraph.fromRel (fun a b : ↥S =>
        plaquetteTouches a.1 b.1)).Reachable x y :=
      Finpartition.mem_part_ofSetoid_iff_rel.mp hyPx
    have hxe : x = ⟨p, hp⟩ := Subtype.ext hxp
    exact ⟨y, hxe ▸ hreach, hyq ▸ hq'⟩
  · rintro ⟨q, hreach, hq⟩
    rw [nearLoop, Finset.mem_biUnion]
    refine ⟨((Finpartition.ofSetoid
        ((SimpleGraph.fromRel (fun a b : ↥S =>
          plaquetteTouches a.1 b.1)).reachableSetoid)).part
            ⟨p, hp⟩).image Subtype.val, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨?_, q.1, Finset.mem_image_of_mem _
        (Finpartition.mem_part_ofSetoid_iff_rel.mpr hreach), hq⟩
      unfold plaqComponents
      rw [Finset.mem_image]
      exact ⟨_, (Finpartition.ofSetoid _).part_mem.mpr
        (Finset.mem_univ _), rfl⟩
    · have hrr : (SimpleGraph.fromRel (fun a b : ↥S =>
          plaquetteTouches a.1 b.1)).Reachable ⟨p, hp⟩ ⟨p, hp⟩ :=
        SimpleGraph.Reachable.refl _
      have hself : (⟨p, hp⟩ : ↥S) ∈ (Finpartition.ofSetoid
          ((SimpleGraph.fromRel (fun a b : ↥S =>
            plaquetteTouches a.1 b.1)).reachableSetoid)).part ⟨p, hp⟩ :=
        Finpartition.mem_part_ofSetoid_iff_rel.mpr hrr
      exact Finset.mem_image_of_mem _ hself

open Classical in
/-- **Walk confinement (V1-b step 2):** in the touching graph of a
union `S₀ ∪ T` with NO cross-touching, a walk starting at a `T`-vertex
never leaves `T`. -/
theorem walk_confined {S₀ T : Finset (ConcretePlaquette d N)}
    (hcross : ∀ q ∈ S₀, ∀ p ∈ T, ¬ plaquetteTouches q p)
    {x y : ↥(S₀ ∪ T)}
    (W : (SimpleGraph.fromRel (fun a b : ↥(S₀ ∪ T) =>
      plaquetteTouches a.1 b.1)).Walk x y) :
    x.1 ∈ T → y.1 ∈ T := by
  induction W with
  | nil => exact id
  | @cons u v w h W ih =>
      intro hu
      refine ih ?_
      rw [SimpleGraph.fromRel_adj] at h
      obtain ⟨-, htouch⟩ := h
      rcases Finset.mem_union.mp v.2 with hv | hv
      · exfalso
        rcases htouch with ht | ht
        · exact hcross v.1 hv u.1 hu (fun hd => ht (Disjoint.symm hd))
        · exact hcross v.1 hv u.1 hu ht
      · exact hv

open Classical in
/-- **Walk lifting (V1-b step 3):** reachability in `S₀`'s touching
graph transports to the union's graph along the inclusion. -/
theorem reachable_union_of_reachable
    {S₀ T : Finset (ConcretePlaquette d N)} {a b : ↥S₀}
    (h : (SimpleGraph.fromRel (fun u v : ↥S₀ =>
      plaquetteTouches u.1 v.1)).Reachable a b) :
    (SimpleGraph.fromRel (fun u v : ↥(S₀ ∪ T) =>
      plaquetteTouches u.1 v.1)).Reachable
      ⟨a.1, Finset.mem_union_left T a.2⟩
      ⟨b.1, Finset.mem_union_left T b.2⟩ := by
  classical
  exact h.map
    (⟨fun a => ⟨a.1, Finset.mem_union_left T a.2⟩, by
      intro a b hab
      rw [SimpleGraph.fromRel_adj] at hab ⊢
      refine ⟨fun h => hab.1 ?_, hab.2⟩
      have h2 := congrArg Subtype.val h
      exact Subtype.ext h2⟩ :
      (SimpleGraph.fromRel (fun u v : ↥S₀ =>
        plaquetteTouches u.1 v.1)) →g
      (SimpleGraph.fromRel (fun u v : ↥(S₀ ∪ T) =>
        plaquetteTouches u.1 v.1)))

open Classical in
/-- **Walk descent (V1-b step 4):** in the union's touching graph,
a walk starting at an `S₀`-vertex stays in `S₀` (no cross-touching)
and descends to `S₀`-reachability. -/
theorem reachable_descend {S₀ T : Finset (ConcretePlaquette d N)}
    (hcross : ∀ q ∈ S₀, ∀ p ∈ T, ¬ plaquetteTouches q p)
    {x y : ↥(S₀ ∪ T)}
    (W : (SimpleGraph.fromRel (fun u v : ↥(S₀ ∪ T) =>
      plaquetteTouches u.1 v.1)).Walk x y) :
    ∀ hx : x.1 ∈ S₀, ∃ hy : y.1 ∈ S₀,
      (SimpleGraph.fromRel (fun u v : ↥S₀ =>
        plaquetteTouches u.1 v.1)).Reachable ⟨x.1, hx⟩ ⟨y.1, hy⟩ := by
  induction W with
  | nil => exact fun hx => ⟨hx, SimpleGraph.Reachable.refl _⟩
  | @cons u v w h W ih =>
      intro hu
      rw [SimpleGraph.fromRel_adj] at h
      obtain ⟨hne, htouch⟩ := h
      have hv : v.1 ∈ S₀ := by
        rcases Finset.mem_union.mp v.2 with hv | hv
        · exact hv
        · exfalso
          rcases htouch with ht | ht
          · exact hcross u.1 hu v.1 hv ht
          · exact hcross u.1 hu v.1 hv (fun hd => ht (Disjoint.symm hd))
      obtain ⟨hw, hreach⟩ := ih hv
      refine ⟨hw, SimpleGraph.Reachable.trans
        (SimpleGraph.Adj.reachable ?_) hreach⟩
      rw [SimpleGraph.fromRel_adj]
      refine ⟨fun hval => hne (Subtype.ext ?_), htouch⟩
      have h2 := congrArg Subtype.val hval
      exact h2

/-! ## V1 opening: the far resummation

Summing the far factor of `integral_wilson_obs_regroup` over all far
subsets reconstitutes a RESTRICTED partition function — the object the
`Z`-ratio cancellation (V1) divides against. -/

/-- Binomial expansion of `∏ (1 + w)` over an arbitrary finite index
set, `ℂ`-valued (the banked `prod_one_add_eq_sum` is `ℝ`-valued and
`univ`-only). -/
theorem prod_one_add_eq_sum_powerset {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (w : ι → ℂ) :
    ∏ p ∈ F, (1 + w p) = ∑ T ∈ F.powerset, ∏ p ∈ T, w p := by
  have hcomm : ∀ p ∈ F, 1 + w p = w p + 1 := fun p _ => by ring
  rw [Finset.prod_congr rfl hcomm, Finset.prod_add]
  exact Finset.sum_congr rfl fun t _ => by
    rw [Finset.prod_const_one, mul_one]

open Classical in
/-- **The far resummation:** the sum of the far integrals over ALL
subsets of a far region `F` is the restricted partition function
`∫ ∏_{p∈F}(1 + f_p)`. -/
theorem sum_integral_prod_eq_integral_prod_one_add
    (μ : Measure G) [IsProbabilityMeasure μ]
    (f : ConcretePlaquette d N → GaugeConfig d N G → ℂ)
    (F : Finset (ConcretePlaquette d N))
    (hint : ∀ T ∈ F.powerset, Integrable (fun A => ∏ p ∈ T, f p A)
      (gaugeMeasureFrom (d := d) (N := N) μ)) :
    ∑ T ∈ F.powerset, ∫ A, ∏ p ∈ T, f p A
        ∂(gaugeMeasureFrom (d := d) (N := N) μ)
      = ∫ A, ∏ p ∈ F, (1 + f p A)
          ∂(gaugeMeasureFrom (d := d) (N := N) μ) := by
  rw [← MeasureTheory.integral_finset_sum _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun A => ?_)
  exact (prod_one_add_eq_sum_powerset F (fun p => f p A)).symm

/-- The Wilson-loop instantiation of the V0 headline: a loop
observable times activities supported away from the loop. -/
theorem integral_wilson_obs_mul_prod_split
    (μ : Measure G) [IsProbabilityMeasure μ] {ι : Type*}
    (s : Finset ι) (φ : G → ℂ) (es : List (ConcreteEdge d N))
    (g : ι → GaugeConfig d N G → ℂ) (Sg : ι → Finset (PosEdge d N))
    (hg : ∀ i ∈ s, DependsOnPos (g i) (Sg i))
    (hdisj : ∀ i ∈ s, Disjoint (edgeSupport es) (Sg i)) :
    ∫ A, φ (wilsonLine A es) * ∏ i ∈ s, g i A
        ∂(gaugeMeasureFrom (d := d) (N := N) μ)
      = (∫ A, φ (wilsonLine A es) ∂(gaugeMeasureFrom (d := d) (N := N) μ)) *
        ∫ A, ∏ i ∈ s, g i A ∂(gaugeMeasureFrom (d := d) (N := N) μ) :=
  integral_mul_prod_of_disjoint_support μ s _ g (edgeSupport es) Sg
    (dependsOnPos_comp_wilsonLine φ es) hg hdisj

end YangMills
