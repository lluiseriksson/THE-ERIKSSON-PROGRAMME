/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.L1_GibbsMeasure.LocalWindowGeometry
import YangMills.L1_GibbsMeasure.LocalMarkedExpansion

/-!
# Stability of local activities across finite volumes

Common-window plaquettes have the same Mayer weights in every fitting torus
when the corresponding positive-edge coordinates agree.  Combining this
pointwise fact with the finite-marginal bridge gives equality of the
integrated activity of every finite common-window plaquette set.

No map between complete gauge configurations is used.
-/

namespace YangMills

open MeasureTheory GaugeConfig

private theorem posToConfig_apply_positive
    {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    (x : PosEdge d N → G) (e : PosEdge d N) :
    posToConfig x e.1 = x e := by
  have h :=
    congrFun
      ((gaugeConfigEquiv (d := d) (N := N) (G := G)).left_inv x) e
  exact h

private theorem posToConfig_apply_negative
    {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    (x : PosEdge d N → G) (e : ConcreteEdge d N)
    (he : e.sign = false) :
    posToConfig x e = (x e.pos)⁻¹ := by
  simp [posToConfig, posToFun, ConcreteEdge.pos, he]

/-- A realized common-window plaquette has the expected four coordinate
values: two positive boundary edges followed by the inverses of the other
two positive representatives. -/
theorem WindowPlaquette.plaquetteHolonomy_posToConfig
    {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    (p : WindowPlaquette d) (hp : p.Fits N)
    (x : PosEdge d N → G) :
    plaquetteHolonomy (posToConfig x) (p.toConcrete hp)
      =
      x ((p.posEdge 0).toPosEdge (p.posEdge_fits hp 0)) *
      x ((p.posEdge 1).toPosEdge (p.posEdge_fits hp 1)) *
      (x ((p.posEdge 2).toPosEdge (p.posEdge_fits hp 2)))⁻¹ *
      (x ((p.posEdge 3).toPosEdge (p.posEdge_fits hp 3)))⁻¹ := by
  unfold plaquetteHolonomy
  have h0 :
      posToConfig x ((p.toConcrete hp).edges 0) =
        x ((p.posEdge 0).toPosEdge (p.posEdge_fits hp 0)) := by
    rw [← p.toConcrete_edge_pos hp 0]
    exact posToConfig_apply_positive x
      ((p.toConcrete hp).edges 0).pos
  have h1 :
      posToConfig x ((p.toConcrete hp).edges 1) =
        x ((p.posEdge 1).toPosEdge (p.posEdge_fits hp 1)) := by
    rw [← p.toConcrete_edge_pos hp 1]
    exact posToConfig_apply_positive x
      ((p.toConcrete hp).edges 1).pos
  have h2 :
      posToConfig x ((p.toConcrete hp).edges 2) =
        (x ((p.posEdge 2).toPosEdge (p.posEdge_fits hp 2)))⁻¹ := by
    rw [← p.toConcrete_edge_pos hp 2]
    exact posToConfig_apply_negative x
      ((p.toConcrete hp).edges 2) rfl
  have h3 :
      posToConfig x ((p.toConcrete hp).edges 3) =
        (x ((p.posEdge 3).toPosEdge (p.posEdge_fits hp 3)))⁻¹ := by
    rw [← p.toConcrete_edge_pos hp 3]
    exact posToConfig_apply_negative x
      ((p.toConcrete hp).edges 3) rfl
  change
    posToConfig x ((p.toConcrete hp).edges 0) *
      posToConfig x ((p.toConcrete hp).edges 1) *
      posToConfig x ((p.toConcrete hp).edges 2) *
      posToConfig x ((p.toConcrete hp).edges 3) = _
  rw [h0, h1, h2, h3]

/-- Corresponding positive-edge assignments give identical Mayer weights
for a common-window plaquette in two different fitting tori. -/
theorem WindowPlaquette.plaquetteWeight_toConcrete_eq
    {d N M : ℕ} [NeZero d] [NeZero N] [NeZero M]
    {G : Type*} [Group G] [MeasurableSpace G]
    (pe : G → ℝ) (β : ℝ)
    (p : WindowPlaquette d) (hN : p.Fits N) (hM : p.Fits M)
    (xN : PosEdge d N → G) (xM : PosEdge d M → G)
    (hcoord : ∀ k : Fin 4,
      xN ((p.posEdge k).toPosEdge (p.posEdge_fits hN k)) =
        xM ((p.posEdge k).toPosEdge (p.posEdge_fits hM k))) :
    plaquetteWeight pe β (posToConfig xN) (p.toConcrete hN) =
      plaquetteWeight pe β (posToConfig xM) (p.toConcrete hM) := by
  unfold plaquetteWeight
  rw [p.plaquetteHolonomy_posToConfig hN xN,
    p.plaquetteHolonomy_posToConfig hM xM]
  rw [hcoord 0, hcoord 1, hcoord 2, hcoord 3]

open Classical in
/-- **Cross-volume activity stability.**  The integrated Mayer monomial of a
finite common-window plaquette set is identical in every pair of fitting
tori.  The proof uses only the induced equivalence of its finite positive
edge supports. -/
theorem integral_prod_plaquetteWeight_realizedFinset_eq
    {d N M : ℕ} [NeZero d] [NeZero N] [NeZero M]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (S : Finset (WindowPlaquette d))
    (hN : ∀ p ∈ S, p.Fits N) (hM : ∀ p ∈ S, p.Fits M) :
    (∫ A, ∏ p ∈ WindowPlaquette.realizedFinset S hN,
        (plaquetteWeight pe β A p : ℂ)
      ∂(gaugeMeasureFrom (d := d) (N := N) μ))
      =
    ∫ A, ∏ p ∈ WindowPlaquette.realizedFinset S hM,
        (plaquetteWeight pe β A p : ℂ)
      ∂(gaugeMeasureFrom (d := d) (N := M) μ) := by
  classical
  let E := WindowPlaquette.edgeSupport S
  let eN : ∀ e ∈ E, e.Fits N :=
    WindowPlaquette.edgeSupport_fits hN
  let eM : ∀ e ∈ E, e.Fits M :=
    WindowPlaquette.edgeSupport_fits hM
  let SN := WindowPlaquette.realizedFinset S hN
  let SM := WindowPlaquette.realizedFinset S hM
  let EN := WindowPosEdge.realizedFinset E eN
  let EM := WindowPosEdge.realizedFinset E eM
  let FN : GaugeConfig d N G → ℂ :=
    fun A => ∏ p ∈ SN, (plaquetteWeight pe β A p : ℂ)
  let FM : GaugeConfig d M G → ℂ :=
    fun A => ∏ p ∈ SM, (plaquetteWeight pe β A p : ℂ)
  have hFN : DependsOnPos FN EN := by
    refine DependsOnPos.finset_prod SN
      (fun p A => (plaquetteWeight pe β A p : ℂ)) EN ?_
    intro p hp
    refine (dependsOnPos_plaquetteWeight_ofReal pe β p).mono ?_
    rw [show EN =
        SN.biUnion plaquetteSupport by
          dsimp only [EN, SN, E, eN]
          exact
            (WindowPlaquette.biUnion_support_realizedFinset hN).symm]
    exact Finset.subset_biUnion_of_mem plaquetteSupport hp
  have hFM : DependsOnPos FM EM := by
    refine DependsOnPos.finset_prod SM
      (fun p A => (plaquetteWeight pe β A p : ℂ)) EM ?_
    intro p hp
    refine (dependsOnPos_plaquetteWeight_ofReal pe β p).mono ?_
    rw [show EM =
        SM.biUnion plaquetteSupport by
          dsimp only [EM, SM, E, eM]
          exact
            (WindowPlaquette.biUnion_support_realizedFinset hM).symm]
    exact Finset.subset_biUnion_of_mem plaquetteSupport hp
  change (∫ A, FN A ∂(gaugeMeasureFrom (d := d) (N := N) μ)) =
    ∫ A, FM A ∂(gaugeMeasureFrom (d := d) (N := M) μ)
  refine integral_gaugeMeasureFrom_eq_of_supportEquiv
    μ EN EM FN FM hFN hFM
      (WindowPosEdge.realizedSupportEquiv E eN eM) 1 ?_
  intro a
  dsimp only [FN, FM, SN, SM]
  rw [WindowPlaquette.prod_realizedFinset (S := S) hN,
    WindowPlaquette.prod_realizedFinset (S := S) hM]
  refine Finset.prod_congr rfl fun p _ => ?_
  apply congrArg (fun r : ℝ => (r : ℂ))
  apply p.1.plaquetteWeight_toConcrete_eq pe β
  intro k
  have hek : p.1.posEdge k ∈ E := by
    dsimp only [E]
    apply Finset.mem_biUnion.mpr
    exact ⟨p.1, p.2,
      WindowPlaquette.mem_boundaryEdges_iff.mpr ⟨k, rfl⟩⟩
  have hcoord :=
    WindowPosEdge.extend_realizedSupportEquiv_apply
      E eN eM (1 : G) a ⟨p.1.posEdge k, hek⟩
  simpa [WindowPosEdge.realizedEquiv] using hcoord

open Classical in
/-- Pointwise version of activity stability, allowing the plaquette support
to sit inside a larger common-window support (for example, after adjoining a
local observable support). -/
theorem prod_plaquetteWeight_toConcrete_extend_eq
    {d N M : ℕ} [NeZero d] [NeZero N] [NeZero M]
    {G : Type*} [Group G] [MeasurableSpace G]
    (pe : G → ℝ) (β : ℝ)
    (S : Finset (WindowPlaquette d))
    (hN : ∀ p ∈ S, p.Fits N) (hM : ∀ p ∈ S, p.Fits M)
    (U : Finset (WindowPosEdge d))
    (hEU : WindowPlaquette.edgeSupport S ⊆ U)
    (uN : ∀ e ∈ U, e.Fits N) (uM : ∀ e ∈ U, e.Fits M)
    (g₀ : G)
    (a : {q : PosEdge d N //
      q ∈ WindowPosEdge.realizedFinset U uN} → G) :
    (∏ p ∈ WindowPlaquette.realizedFinset S hN,
      plaquetteWeight pe β
        (posToConfig
          (extendOnFinset
            (fun q : PosEdge d N =>
              q ∈ WindowPosEdge.realizedFinset U uN) g₀ a)) p)
      =
    ∏ p ∈ WindowPlaquette.realizedFinset S hM,
      plaquetteWeight pe β
        (posToConfig
          (extendOnFinset
            (fun q : PosEdge d M =>
              q ∈ WindowPosEdge.realizedFinset U uM) g₀
            (fun t => a
              ((WindowPosEdge.realizedSupportEquiv U uN uM).symm t)))) p := by
  rw [WindowPlaquette.prod_realizedFinset (S := S) hN,
    WindowPlaquette.prod_realizedFinset (S := S) hM]
  refine Finset.prod_congr rfl fun p _ => ?_
  apply p.1.plaquetteWeight_toConcrete_eq pe β
  intro k
  have hek : p.1.posEdge k ∈ U := by
    apply hEU
    apply Finset.mem_biUnion.mpr
    exact ⟨p.1, p.2,
      WindowPlaquette.mem_boundaryEdges_iff.mpr ⟨k, rfl⟩⟩
  have hcoord :=
    WindowPosEdge.extend_realizedSupportEquiv_apply
      U uN uM g₀ a ⟨p.1.posEdge k, hek⟩
  simpa [WindowPosEdge.realizedEquiv] using hcoord

namespace CompatibleLocalObservable

/-- The volume-independent coordinate of one abstract observable edge as a
common-window positive edge. -/
def windowEdge
    {d : ℕ} [NeZero d] {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (s : O.Support) :
    WindowPosEdge d :=
  ⟨(O.coord s).1, (O.coord s).2⟩

/-- The abstract observable support embeds in common-window edges. -/
def windowEdgeEmbedding
    {d : ℕ} [NeZero d] {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) :
    O.Support ↪ WindowPosEdge d where
  toFun := O.windowEdge
  inj' := by
    intro s t hst
    apply O.coord_injective
    exact Prod.ext
      (congrArg WindowPosEdge.source hst)
      (congrArg WindowPosEdge.dir hst)

/-- Finite common-window support of a compatible local observable. -/
noncomputable def windowSupport
    {d : ℕ} [NeZero d] {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) :
    Finset (WindowPosEdge d) :=
  Finset.univ.map O.windowEdgeEmbedding

@[simp]
theorem windowEdge_mem_windowSupport
    {d : ℕ} [NeZero d] {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (s : O.Support) :
    O.windowEdge s ∈ O.windowSupport :=
  Finset.mem_map.mpr ⟨s, Finset.mem_univ s, rfl⟩

/-- Every observable window edge fits in every admissible torus. -/
theorem windowSupport_fits
    {d : ℕ} [NeZero d] {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (n : ℕ)
    (hvol : O.minVolume ≤ n) :
    ∀ e ∈ O.windowSupport, e.Fits (n + 1) := by
  intro e he
  obtain ⟨s, -, rfl⟩ := Finset.mem_map.mp he
  intro j
  exact lt_of_lt_of_le (O.coord_lt s j) (by omega)

/-- Realizing one common-window observable edge agrees with the original
`edgeAt`; admissibility removes the modulo reduction. -/
theorem windowEdge_toPosEdge
    {d : ℕ} [NeZero d] {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (n : ℕ)
    (hvol : O.minVolume ≤ n) (s : O.Support) :
    (O.windowEdge s).toPosEdge
        (O.windowSupport_fits n hvol _ (O.windowEdge_mem_windowSupport s))
      = O.edgeAt n hvol s := by
  apply Subtype.ext
  change ConcreteEdge.mk _ _ true = ConcreteEdge.mk _ _ true
  congr 1
  funext j
  apply Fin.ext
  change (O.coord s).1 j = (O.coord s).1 j % (n + 1)
  rw [Nat.mod_eq_of_lt
    (lt_of_lt_of_le (O.coord_lt s j) (by omega))]

open Classical in
/-- The torus realization of the common-window support is exactly the
pre-existing `realizedSupport` of the observable. -/
theorem realizedFinset_windowSupport
    {d : ℕ} [NeZero d] {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (n : ℕ)
    (hvol : O.minVolume ≤ n) :
    WindowPosEdge.realizedFinset O.windowSupport
      (O.windowSupport_fits n hvol)
      = O.realizedSupport n hvol := by
  ext e
  constructor
  · intro he
    obtain ⟨q, hq⟩ :=
      WindowPosEdge.mem_realizedFinset_iff.mp he
    obtain ⟨s, -, hs⟩ := Finset.mem_map.mp q.2
    have hqsub :
        q = ⟨O.windowEdge s, O.windowEdge_mem_windowSupport s⟩ := by
      apply Subtype.ext
      exact hs.symm
    subst q
    rw [O.windowEdge_toPosEdge n hvol s] at hq
    rw [← hq]
    exact O.edgeAt_mem_realizedSupport n hvol s
  · intro he
    rw [CompatibleLocalObservable.realizedSupport,
      Finset.mem_map] at he
    obtain ⟨s, -, rfl⟩ := he
    apply WindowPosEdge.mem_realizedFinset_iff.mpr
    refine ⟨⟨O.windowEdge s, O.windowEdge_mem_windowSupport s⟩, ?_⟩
    exact O.windowEdge_toPosEdge n hvol s

/-- Corresponding assignments on any common-window support containing the
observable support give identical realizations in two admissible volumes. -/
theorem realize_posToConfig_extend_eq
    {d : ℕ} [NeZero d] {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G)
    (n m : ℕ) (hn : O.minVolume ≤ n) (hm : O.minVolume ≤ m)
    (U : Finset (WindowPosEdge d)) (hOU : O.windowSupport ⊆ U)
    (uN : ∀ e ∈ U, e.Fits (n + 1))
    (uM : ∀ e ∈ U, e.Fits (m + 1))
    (g₀ : G)
    (a : {q : PosEdge d (n + 1) //
      q ∈ WindowPosEdge.realizedFinset U uN} → G) :
    O.realize n
        (posToConfig
          (extendOnFinset
            (fun q : PosEdge d (n + 1) =>
              q ∈ WindowPosEdge.realizedFinset U uN) g₀ a))
      =
    O.realize m
        (posToConfig
          (extendOnFinset
            (fun q : PosEdge d (m + 1) =>
              q ∈ WindowPosEdge.realizedFinset U uM) g₀
            (fun t => a
              ((WindowPosEdge.realizedSupportEquiv U uN uM).symm t)))) := by
  rw [CompatibleLocalObservable.realize, dif_pos hn,
    CompatibleLocalObservable.realize, dif_pos hm]
  apply congrArg O.kernel
  funext s
  unfold CompatibleLocalObservable.restrictConfig
  rw [show configToPos
        (posToConfig
          (extendOnFinset
            (fun q : PosEdge d (n + 1) =>
              q ∈ WindowPosEdge.realizedFinset U uN) g₀ a))
      = extendOnFinset
          (fun q : PosEdge d (n + 1) =>
            q ∈ WindowPosEdge.realizedFinset U uN) g₀ a from
        (gaugeConfigEquiv
          (d := d) (N := n + 1) (G := G)).left_inv _,
    show configToPos
        (posToConfig
          (extendOnFinset
            (fun q : PosEdge d (m + 1) =>
              q ∈ WindowPosEdge.realizedFinset U uM) g₀
            (fun t => a
              ((WindowPosEdge.realizedSupportEquiv U uN uM).symm t))))
      = extendOnFinset
          (fun q : PosEdge d (m + 1) =>
            q ∈ WindowPosEdge.realizedFinset U uM) g₀
          (fun t => a
            ((WindowPosEdge.realizedSupportEquiv U uN uM).symm t)) from
        (gaugeConfigEquiv
          (d := d) (N := m + 1) (G := G)).left_inv _]
  change
    extendOnFinset _ _ _ (O.edgeAt n hn s) =
      extendOnFinset _ _ _ (O.edgeAt m hm s)
  rw [← O.windowEdge_toPosEdge n hn s,
    ← O.windowEdge_toPosEdge m hm s]
  have heU : O.windowEdge s ∈ U :=
    hOU (O.windowEdge_mem_windowSupport s)
  have hcoord :=
    WindowPosEdge.extend_realizedSupportEquiv_apply
      U uN uM g₀ a ⟨O.windowEdge s, heU⟩
  simpa [WindowPosEdge.realizedEquiv] using hcoord

end CompatibleLocalObservable

open Classical in
/-- **Cross-volume marked-integral stability.**  A compatible local
observable multiplied by the Mayer monomial of a finite common-window
plaquette set has the same product-Haar integral in every two admissible
fitting volumes. -/
theorem integral_realize_mul_prod_plaquetteWeight_realizedFinset_eq
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (n m : ℕ) (hn : O.minVolume ≤ n) (hm : O.minVolume ≤ m)
    (S : Finset (WindowPlaquette d))
    (hN : ∀ p ∈ S, p.Fits (n + 1))
    (hM : ∀ p ∈ S, p.Fits (m + 1)) :
    (∫ A, (O.realize n A : ℂ) *
        ∏ p ∈ WindowPlaquette.realizedFinset S hN,
          (plaquetteWeight pe β A p : ℂ)
      ∂(gaugeMeasureFrom (d := d) (N := n + 1) μ))
      =
    ∫ A, (O.realize m A : ℂ) *
        ∏ p ∈ WindowPlaquette.realizedFinset S hM,
          (plaquetteWeight pe β A p : ℂ)
      ∂(gaugeMeasureFrom (d := d) (N := m + 1) μ) := by
  classical
  let E := WindowPlaquette.edgeSupport S
  let U := O.windowSupport ∪ E
  let uN : ∀ e ∈ U, e.Fits (n + 1) := by
    intro e he
    rcases Finset.mem_union.mp he with heO | heE
    · exact O.windowSupport_fits n hn e heO
    · exact WindowPlaquette.edgeSupport_fits hN e heE
  let uM : ∀ e ∈ U, e.Fits (m + 1) := by
    intro e he
    rcases Finset.mem_union.mp he with heO | heE
    · exact O.windowSupport_fits m hm e heO
    · exact WindowPlaquette.edgeSupport_fits hM e heE
  let UN := WindowPosEdge.realizedFinset U uN
  let UM := WindowPosEdge.realizedFinset U uM
  let SN := WindowPlaquette.realizedFinset S hN
  let SM := WindowPlaquette.realizedFinset S hM
  let FN : GaugeConfig d (n + 1) G → ℂ :=
    fun A => (O.realize n A : ℂ) *
      ∏ p ∈ SN, (plaquetteWeight pe β A p : ℂ)
  let FM : GaugeConfig d (m + 1) G → ℂ :=
    fun A => (O.realize m A : ℂ) *
      ∏ p ∈ SM, (plaquetteWeight pe β A p : ℂ)
  have hON : DependsOnPos
      (fun A : GaugeConfig d (n + 1) G => (O.realize n A : ℂ)) UN := by
    refine (O.dependsOnPos_realize n hn).mono ?_
    rw [← O.realizedFinset_windowSupport n hn]
    exact WindowPosEdge.realizedFinset_mono
      Finset.subset_union_left (O.windowSupport_fits n hn) uN
  have hOM : DependsOnPos
      (fun A : GaugeConfig d (m + 1) G => (O.realize m A : ℂ)) UM := by
    refine (O.dependsOnPos_realize m hm).mono ?_
    rw [← O.realizedFinset_windowSupport m hm]
    exact WindowPosEdge.realizedFinset_mono
      Finset.subset_union_left (O.windowSupport_fits m hm) uM
  have hPN : DependsOnPos
      (fun A : GaugeConfig d (n + 1) G =>
        ∏ p ∈ SN, (plaquetteWeight pe β A p : ℂ)) UN := by
    refine DependsOnPos.finset_prod SN
      (fun p A => (plaquetteWeight pe β A p : ℂ)) UN ?_
    intro p hp
    refine (dependsOnPos_plaquetteWeight_ofReal pe β p).mono ?_
    apply (Finset.subset_biUnion_of_mem plaquetteSupport hp).trans
    rw [show
        (SN.biUnion plaquetteSupport) =
            WindowPosEdge.realizedFinset E
              (WindowPlaquette.edgeSupport_fits hN) by
          dsimp only [SN, E]
          exact WindowPlaquette.biUnion_support_realizedFinset hN]
    exact WindowPosEdge.realizedFinset_mono
        Finset.subset_union_right
        (WindowPlaquette.edgeSupport_fits hN) uN
  have hPM : DependsOnPos
      (fun A : GaugeConfig d (m + 1) G =>
        ∏ p ∈ SM, (plaquetteWeight pe β A p : ℂ)) UM := by
    refine DependsOnPos.finset_prod SM
      (fun p A => (plaquetteWeight pe β A p : ℂ)) UM ?_
    intro p hp
    refine (dependsOnPos_plaquetteWeight_ofReal pe β p).mono ?_
    apply (Finset.subset_biUnion_of_mem plaquetteSupport hp).trans
    rw [show
        (SM.biUnion plaquetteSupport) =
            WindowPosEdge.realizedFinset E
              (WindowPlaquette.edgeSupport_fits hM) by
          dsimp only [SM, E]
          exact WindowPlaquette.biUnion_support_realizedFinset hM]
    exact WindowPosEdge.realizedFinset_mono
        Finset.subset_union_right
        (WindowPlaquette.edgeSupport_fits hM) uM
  have hFN : DependsOnPos FN UN := DependsOnPos.mul hON hPN
  have hFM : DependsOnPos FM UM := DependsOnPos.mul hOM hPM
  change (∫ A, FN A
      ∂(gaugeMeasureFrom (d := d) (N := n + 1) μ)) =
    ∫ A, FM A
      ∂(gaugeMeasureFrom (d := d) (N := m + 1) μ)
  refine integral_gaugeMeasureFrom_eq_of_supportEquiv
    μ UN UM FN FM hFN hFM
      (WindowPosEdge.realizedSupportEquiv U uN uM) 1 ?_
  intro a
  dsimp only [FN, FM]
  have hO := O.realize_posToConfig_extend_eq
    n m hn hm U Finset.subset_union_left uN uM (1 : G) a
  have hP := prod_plaquetteWeight_toConcrete_extend_eq
    pe β S hN hM U Finset.subset_union_right uN uM (1 : G) a
  rw [hO]
  dsimp only [SN, SM, UN, UM]
  congr 1
  have hPc := congrArg (fun r : ℝ => (r : ℂ)) hP
  push_cast at hPc
  exact hPc

end YangMills
