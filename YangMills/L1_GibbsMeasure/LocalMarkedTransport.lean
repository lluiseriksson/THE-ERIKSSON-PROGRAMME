/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.L1_GibbsMeasure.LocalMarkedTail

/-!
# Common-window transport of finite marked sets

A below-cutoff set satisfying `localNear SF S₀ = S₀` can have several
connected components.  Every component nevertheless contains a plaquette
incident to the observable support.  Centering that support with a margin
larger than `|S₀|` therefore places every plaquette of every component in one
volume-independent window.
-/

namespace YangMills

open MeasureTheory GaugeConfig

namespace WindowPolymer

open Classical

/-- Ordinary-coordinate decoding is injective: it forgets only the ambient
finite type, not any site value or plaquette direction. -/
theorem ConcretePlaquette.toWindow_injective
    {d N : ℕ} :
    Function.Injective
      (ConcretePlaquette.toWindow :
        ConcretePlaquette d N → WindowPlaquette d) := by
  intro p q hpq
  rcases p with ⟨ps, pi, pj, hp⟩
  rcases q with ⟨qs, qi, qj, hq⟩
  have hs :
      (fun k => (ps k).val) = (fun k => (qs k).val) := by
    simpa [ConcretePlaquette.toWindow] using
      congrArg WindowPlaquette.site hpq
  have hi : pi = qi := by
    simpa [ConcretePlaquette.toWindow] using
      congrArg WindowPlaquette.dir1 hpq
  have hj : pj = qj := by
    simpa [ConcretePlaquette.toWindow] using
      congrArg WindowPlaquette.dir2 hpq
  have hs' : ps = qs := by
    funext k
    apply Fin.ext
    exact congrFun hs k
  subst qs
  subst qi
  subst qj
  rfl

/-- Injective ordinary-coordinate decoding as a finite-set embedding. -/
def ConcretePlaquette.toWindowEmbedding
    {d N : ℕ} :
    ConcretePlaquette d N ↪ WindowPlaquette d :=
  ⟨ConcretePlaquette.toWindow,
    ConcretePlaquette.toWindow_injective⟩

/-- If a common-window marked set is completely near a common-window edge
support in one fitting torus, it is completely near that support in every
other fitting torus. -/
private theorem localNear_realizedFinset_eq_of_eq
    {d N M : ℕ} [NeZero d] [NeZero N] [NeZero M]
    (U : Finset (WindowPosEdge d))
    (uN : ∀ e ∈ U, e.Fits N)
    (uM : ∀ e ∈ U, e.Fits M)
    (S : Finset (WindowPlaquette d))
    (hN : ∀ p ∈ S, p.Fits N)
    (hM : ∀ p ∈ S, p.Fits M)
    (hnearN :
      localNear (WindowPosEdge.realizedFinset U uN)
          (WindowPlaquette.realizedFinset S hN)
        =
      WindowPlaquette.realizedFinset S hN) :
    localNear (WindowPosEdge.realizedFinset U uM)
        (WindowPlaquette.realizedFinset S hM)
      =
    WindowPlaquette.realizedFinset S hM := by
  apply Finset.Subset.antisymm
    (localNear_subset _ _) ?_
  intro pM hpM
  obtain ⟨p, hpvalM⟩ :=
    WindowPlaquette.mem_realizedFinset_iff.mp hpM
  let φN := WindowPlaquette.realizedGraphIso S hN
  let φM := WindowPlaquette.realizedGraphIso S hM
  have hpNearN : (φN p).1 ∈
      localNear (WindowPosEdge.realizedFinset U uN)
        (WindowPlaquette.realizedFinset S hN) := by
    rw [hnearN]
    exact (φN p).2
  have hpNearN' : (φN p).1 ∈
      nearLoop
        (supportEdgeList (WindowPosEdge.realizedFinset U uN))
        (WindowPlaquette.realizedFinset S hN) := by
    simpa [localNear] using hpNearN
  obtain ⟨qN, hpqN, hqIncN⟩ :=
    (mem_nearLoop_iff_reachable (φN p).2).mp hpNearN'
  let q : ↥S := φN.symm qN
  have hpqWindow :
      (SimpleGraph.fromRel
        (fun a b : ↥S => a.1.Touches b.1)).Reachable p q := by
    have hpqN' :
        (SimpleGraph.fromRel
          (fun a b :
              ↥(WindowPlaquette.realizedFinset S hN) =>
            plaquetteTouches a.1 b.1)).Reachable
          (φN p) (φN q) := by
      simpa [q] using hpqN
    exact
      (SimpleGraph.Iso.reachable_iff (φ := φN)).mp hpqN'
  have hpqM :
      (SimpleGraph.fromRel
        (fun a b :
            ↥(WindowPlaquette.realizedFinset S hM) =>
          plaquetteTouches a.1 b.1)).Reachable
        (φM p) (φM q) :=
    (SimpleGraph.Iso.reachable_iff (φ := φM)).mpr hpqWindow
  have hqSupportN : qN.1 ∈ supportPlaquettes
      (WindowPosEdge.realizedFinset U uN) := by
    obtain ⟨e, heU, heq⟩ :=
      Finset.not_disjoint_iff.mp hqIncN
    apply ConcreteSupport.mem_supportPlaquettes_iff.mpr
    exact ⟨e,
      by simpa [edgeSupport_supportEdgeList] using heU,
      heq⟩
  have hqNval :
      q.1.toConcrete (hN q.1 q.2) = qN.1 := by
    exact congrArg Subtype.val (φN.apply_symm_apply qN)
  rw [← hqNval] at hqSupportN
  have hqSupportM :
      q.1.toConcrete (hM q.1 q.2) ∈ supportPlaquettes
        (WindowPosEdge.realizedFinset U uM) :=
    (WindowPlaquette.mem_supportPlaquettes_realizedFinset_iff
      U uN uM q.1 (hN q.1 q.2) (hM q.1 q.2)).mp
        hqSupportN
  have hqIncM :
      ¬ Disjoint
        (_root_.YangMills.edgeSupport
          (supportEdgeList (WindowPosEdge.realizedFinset U uM)))
        (plaquetteSupport (φM q).1) := by
    obtain ⟨e, heU, heq⟩ :=
      ConcreteSupport.mem_supportPlaquettes_iff.mp hqSupportM
    apply Finset.not_disjoint_iff.mpr
    exact ⟨e,
      by simpa [edgeSupport_supportEdgeList] using heU,
      by simpa [φM, WindowPlaquette.realizedGraphIso,
        WindowPlaquette.realizedEquiv] using heq⟩
  have hpNearM' : (φM p).1 ∈
      nearLoop
        (supportEdgeList (WindowPosEdge.realizedFinset U uM))
        (WindowPlaquette.realizedFinset S hM) :=
    (mem_nearLoop_iff_reachable (φM p).2).mpr
      ⟨φM q, hpqM, hqIncM⟩
  have hpNearM : (φM p).1 ∈
      localNear (WindowPosEdge.realizedFinset U uM)
        (WindowPlaquette.realizedFinset S hM) := by
    simpa [localNear] using hpNearM'
  rw [← hpvalM]
  simpa [φM, WindowPlaquette.realizedGraphIso,
    WindowPlaquette.realizedEquiv] using hpNearM

/-- The fixed-point predicate defining a complete marked set is a genuine
common-window invariant, not merely a one-way implication. -/
theorem localNear_realizedFinset_eq_iff
    {d N M : ℕ} [NeZero d] [NeZero N] [NeZero M]
    (U : Finset (WindowPosEdge d))
    (uN : ∀ e ∈ U, e.Fits N)
    (uM : ∀ e ∈ U, e.Fits M)
    (S : Finset (WindowPlaquette d))
    (hN : ∀ p ∈ S, p.Fits N)
    (hM : ∀ p ∈ S, p.Fits M) :
    localNear (WindowPosEdge.realizedFinset U uN)
        (WindowPlaquette.realizedFinset S hN)
        =
      WindowPlaquette.realizedFinset S hN
      ↔
    localNear (WindowPosEdge.realizedFinset U uM)
        (WindowPlaquette.realizedFinset S hM)
        =
      WindowPlaquette.realizedFinset S hM := by
  constructor
  · exact localNear_realizedFinset_eq_of_eq
      U uN uM S hN hM
  · exact localNear_realizedFinset_eq_of_eq
      U uM uN S hM hN

/-- Every plaquette of a cardinality-bounded marked set avoids the periodic
seam when the centered observable support has the corresponding margin. -/
theorem markedSet_siteMargin_zero
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (R : ℕ)
    (hC : (O.center (R + 2)).minVolume ≤ n)
    (hroom :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    {S₀ : Finset (ConcretePlaquette d (n + 1))}
    (hpin : localNear
      ((O.center (R + 2)).realizedSupport n hC) S₀ = S₀)
    (hcard : S₀.card ≤ R)
    {q : ConcretePlaquette d (n + 1)} (hq : q ∈ S₀) :
    q.SiteMargin 0 := by
  obtain ⟨c, hc, hqc⟩ := mem_plaqComponents_of_mem hq
  obtain ⟨p, hpc, hpTouch⟩ :=
    plaqComponents_touches_of_pinned
      (es := supportEdgeList
        ((O.center (R + 2)).realizedSupport n hC))
      (by simpa [localNear] using hpin) hc
  have hpSupport :
      p ∈ supportPlaquettes
        ((O.center (R + 2)).realizedSupport n hC) := by
    obtain ⟨e, heSF, hep⟩ :=
      Finset.not_disjoint_iff.mp
        (by simpa [edgeSupport_supportEdgeList] using hpTouch)
    exact ConcreteSupport.mem_supportPlaquettes_iff.mpr
      ⟨e, heSF, hep⟩
  have hpMarginR : p.SiteMargin R :=
    O.supportPlaquette_centered_siteMargin R hC hroom hpSupport
  have hcsub : c ⊆ S₀ := plaqComponents_subset hc
  have hcCard : c.card ≤ R :=
    (Finset.card_le_card hcsub).trans hcard
  exact siteMargin_zero_of_mem_connected
    (plaqComponents_isConnectedPolymer hc) hpc hqc
    (hpMarginR.mono hcCard)

/-- The same marked plaquette, decoded through its ordinary coordinates,
fits in every target volume with the identical explicit room bound. -/
theorem markedSet_toWindow_fits_target
    {d n M : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (R : ℕ)
    (hC : (O.center (R + 2)).minVolume ≤ n)
    (hroomN :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    (hroomM :
      O.minVolume + (R + 2) + 1 + R + 1 < M)
    {S₀ : Finset (ConcretePlaquette d (n + 1))}
    (hpin : localNear
      ((O.center (R + 2)).realizedSupport n hC) S₀ = S₀)
    (hcard : S₀.card ≤ R)
    {q : ConcretePlaquette d (n + 1)} (hq : q ∈ S₀) :
    q.toWindow.Fits M := by
  obtain ⟨c, hc, hqc⟩ := mem_plaqComponents_of_mem hq
  obtain ⟨p, hpc, hpTouch⟩ :=
    plaqComponents_touches_of_pinned
      (es := supportEdgeList
        ((O.center (R + 2)).realizedSupport n hC))
      (by simpa [localNear] using hpin) hc
  have hpSupport :
      p ∈ supportPlaquettes
        ((O.center (R + 2)).realizedSupport n hC) := by
    obtain ⟨e, heSF, hep⟩ :=
      Finset.not_disjoint_iff.mp
        (by simpa [edgeSupport_supportEdgeList] using hpTouch)
    exact ConcreteSupport.mem_supportPlaquettes_iff.mpr
      ⟨e, heSF, hep⟩
  have hpMarginR : p.SiteMargin R :=
    O.supportPlaquette_centered_siteMargin R hC hroomN hpSupport
  have hpTargetR : ∀ j, (p.site j).val + R + 1 < M :=
    O.supportPlaquette_centered_targetRoom R hC hroomM hpSupport
  obtain ⟨W, hW⟩ :=
    exists_touchWalk_of_connected
      (plaqComponents_isConnectedPolymer hc) hpc hqc
  have hcsub : c ⊆ S₀ := plaqComponents_subset hc
  have hWR : W.length ≤ R := by
    have hcCard : c.card ≤ R :=
      (Finset.card_le_card hcsub).trans hcard
    omega
  have hpMarginW : p.SiteMargin W.length :=
    hpMarginR.mono hWR
  have hpTargetW :
      ∀ j, (p.site j).val + W.length + 1 < M := by
    intro j
    have := hpTargetR j
    omega
  exact ConcretePlaquette.site_add_one_lt_of_touchWalk
    W hpMarginW hpTargetW

/-- A sharper form of seam avoidance: after paying at most `K` touching
steps inside the marked component, every marked plaquette retains any
residual margin `r` with `r + K ≤ R`. -/
theorem markedSet_siteMargin_residual
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (R K r : ℕ)
    (hC : (O.center (R + 2)).minVolume ≤ n)
    (hroom :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    {S₀ : Finset (ConcretePlaquette d (n + 1))}
    (hpin : localNear
      ((O.center (R + 2)).realizedSupport n hC) S₀ = S₀)
    (hcard : S₀.card ≤ K) (hres : r + K ≤ R)
    {q : ConcretePlaquette d (n + 1)} (hq : q ∈ S₀) :
    q.SiteMargin r := by
  obtain ⟨c, hc, hqc⟩ := mem_plaqComponents_of_mem hq
  obtain ⟨p, hpc, hpTouch⟩ :=
    plaqComponents_touches_of_pinned
      (es := supportEdgeList
        ((O.center (R + 2)).realizedSupport n hC))
      (by simpa [localNear] using hpin) hc
  have hpSupport :
      p ∈ supportPlaquettes
        ((O.center (R + 2)).realizedSupport n hC) := by
    obtain ⟨e, heSF, hep⟩ := Finset.not_disjoint_iff.mp
      (by simpa [edgeSupport_supportEdgeList] using hpTouch)
    exact ConcreteSupport.mem_supportPlaquettes_iff.mpr
      ⟨e, heSF, hep⟩
  have hpMarginR : p.SiteMargin R :=
    O.supportPlaquette_centered_siteMargin
      R hC hroom hpSupport
  obtain ⟨W, hW⟩ :=
    exists_touchWalk_of_connected
      (plaqComponents_isConnectedPolymer hc) hpc hqc
  have hcsub : c ⊆ S₀ := plaqComponents_subset hc
  have hWK : W.length ≤ K := by
    have hcCard : c.card ≤ K :=
      (Finset.card_le_card hcsub).trans hcard
    omega
  exact ConcretePlaquette.siteMargin_of_touchWalk W
    (hpMarginR.mono (by omega))

/-- Residual upper room is propagated through the same marked component.
This is the target-volume companion to `markedSet_siteMargin_residual`. -/
theorem markedSet_targetRoom_residual
    {d n M : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (R K r : ℕ)
    (hC : (O.center (R + 2)).minVolume ≤ n)
    (hroomN :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    (hroomM :
      O.minVolume + (R + 2) + 1 + R + 1 < M)
    {S₀ : Finset (ConcretePlaquette d (n + 1))}
    (hpin : localNear
      ((O.center (R + 2)).realizedSupport n hC) S₀ = S₀)
    (hcard : S₀.card ≤ K) (hres : r + K ≤ R)
    {q : ConcretePlaquette d (n + 1)} (hq : q ∈ S₀) :
    ∀ j, (q.site j).val + r + 1 < M := by
  obtain ⟨c, hc, hqc⟩ := mem_plaqComponents_of_mem hq
  obtain ⟨p, hpc, hpTouch⟩ :=
    plaqComponents_touches_of_pinned
      (es := supportEdgeList
        ((O.center (R + 2)).realizedSupport n hC))
      (by simpa [localNear] using hpin) hc
  have hpSupport :
      p ∈ supportPlaquettes
        ((O.center (R + 2)).realizedSupport n hC) := by
    obtain ⟨e, heSF, hep⟩ := Finset.not_disjoint_iff.mp
      (by simpa [edgeSupport_supportEdgeList] using hpTouch)
    exact ConcreteSupport.mem_supportPlaquettes_iff.mpr
      ⟨e, heSF, hep⟩
  have hpMarginR : p.SiteMargin R :=
    O.supportPlaquette_centered_siteMargin
      R hC hroomN hpSupport
  have hpTargetR : ∀ j, (p.site j).val + R + 1 < M :=
    O.supportPlaquette_centered_targetRoom
      R hC hroomM hpSupport
  obtain ⟨W, hW⟩ :=
    exists_touchWalk_of_connected
      (plaqComponents_isConnectedPolymer hc) hpc hqc
  have hcsub : c ⊆ S₀ := plaqComponents_subset hc
  have hWK : W.length ≤ K := by
    have hcCard : c.card ≤ K :=
      (Finset.card_le_card hcsub).trans hcard
    omega
  have hpMarginW : p.SiteMargin W.length :=
    hpMarginR.mono (by omega)
  intro j
  have hqj :=
    ConcretePlaquette.site_le_add_length_of_touchWalk
      W hpMarginW j
  have hpj := hpTargetR j
  omega

/-- Every plaquette incident to the combined support of the observable and
a small complete marked set has enough bilateral margin to anchor a second
below-cutoff cluster. -/
theorem unionMarkedSupport_siteMargin
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (R K L : ℕ)
    (hC : (O.center (R + 2)).minVolume ≤ n)
    (hroom :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    {S₀ : Finset (ConcretePlaquette d (n + 1))}
    (hpin : localNear
      ((O.center (R + 2)).realizedSupport n hC) S₀ = S₀)
    (hcard : S₀.card ≤ K)
    (hres : (2 * L + 1) + K ≤ R)
    {p : ConcretePlaquette d (n + 1)}
    (hp : p ∈ supportPlaquettes
      (((O.center (R + 2)).realizedSupport n hC) ∪
        S₀.biUnion plaquetteSupport)) :
    p.SiteMargin (2 * L) := by
  obtain ⟨e, heU, hep⟩ :=
    ConcreteSupport.mem_supportPlaquettes_iff.mp hp
  rcases Finset.mem_union.mp heU with heSF | heS₀
  · have hpSF : p ∈ supportPlaquettes
        ((O.center (R + 2)).realizedSupport n hC) :=
      ConcreteSupport.mem_supportPlaquettes_iff.mpr
        ⟨e, heSF, hep⟩
    exact (O.supportPlaquette_centered_siteMargin
      R hC hroom hpSF).mono (by omega)
  · obtain ⟨q, hqS₀, heq⟩ :=
      Finset.mem_biUnion.mp heS₀
    have hqMargin : q.SiteMargin (2 * L + 1) :=
      markedSet_siteMargin_residual
        O R K (2 * L + 1) hC hroom hpin hcard hres hqS₀
    have htouch : plaquetteTouches q p :=
      Finset.not_disjoint_iff.mpr ⟨e, heq, hep⟩
    exact ConcretePlaquette.siteMargin_of_touches
      hqMargin htouch

/-- Target-volume upper room for the same combined-support anchor. -/
theorem unionMarkedSupport_targetRoom
    {d n M : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (R K L : ℕ)
    (hC : (O.center (R + 2)).minVolume ≤ n)
    (hroomN :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    (hroomM :
      O.minVolume + (R + 2) + 1 + R + 1 < M)
    {S₀ : Finset (ConcretePlaquette d (n + 1))}
    (hpin : localNear
      ((O.center (R + 2)).realizedSupport n hC) S₀ = S₀)
    (hcard : S₀.card ≤ K)
    (hres : (2 * L + 1) + K ≤ R)
    {p : ConcretePlaquette d (n + 1)}
    (hp : p ∈ supportPlaquettes
      (((O.center (R + 2)).realizedSupport n hC) ∪
        S₀.biUnion plaquetteSupport)) :
    ∀ j, (p.site j).val + 2 * L + 1 < M := by
  obtain ⟨e, heU, hep⟩ :=
    ConcreteSupport.mem_supportPlaquettes_iff.mp hp
  rcases Finset.mem_union.mp heU with heSF | heS₀
  · have hpSF : p ∈ supportPlaquettes
        ((O.center (R + 2)).realizedSupport n hC) :=
      ConcreteSupport.mem_supportPlaquettes_iff.mpr
        ⟨e, heSF, hep⟩
    intro j
    have hpj :=
      O.supportPlaquette_centered_targetRoom
        R hC hroomM hpSF j
    omega
  · obtain ⟨q, hqS₀, heq⟩ :=
      Finset.mem_biUnion.mp heS₀
    have hqMargin : q.SiteMargin (2 * L + 1) :=
      markedSet_siteMargin_residual
        O R K (2 * L + 1) hC hroomN hpin hcard hres hqS₀
    have hqTarget :
        ∀ j, (q.site j).val + (2 * L + 1) + 1 < M :=
      markedSet_targetRoom_residual
        O R K (2 * L + 1) hC hroomN hroomM
          hpin hcard hres hqS₀
    have htouch : plaquetteTouches q p :=
      Finset.not_disjoint_iff.mpr ⟨e, heq, hep⟩
    by_cases hpq : q = p
    · subst p
      intro j
      have := hqTarget j
      omega
    · have hadj : (touchGraph d (n + 1)).Adj q p := by
        show (SimpleGraph.fromRel plaquetteTouches).Adj q p
        rw [SimpleGraph.fromRel_adj]
        exact ⟨hpq, Or.inl htouch⟩
      let W : (touchGraph d (n + 1)).Walk q p :=
        SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil
      have hWlen : W.length = 1 := by
        simp [W]
      have hqMarginW : q.SiteMargin W.length := by
        apply hqMargin.mono
        rw [hWlen]
        omega
      intro j
      have hpj :=
        ConcretePlaquette.site_le_add_length_of_touchWalk
          W hqMarginW j
      have hqj := hqTarget j
      rw [hWlen] at hpj
      omega

/-- The volume-independent plaquette set obtained by decoding every member of
a seam-avoiding marked set. -/
noncomputable def decodedMarkedSet
    {d N : ℕ} (S₀ : Finset (ConcretePlaquette d N)) :
    Finset (WindowPlaquette d) :=
  S₀.map ConcretePlaquette.toWindowEmbedding

@[simp]
theorem card_decodedMarkedSet
    {d N : ℕ} (S₀ : Finset (ConcretePlaquette d N)) :
    (decodedMarkedSet S₀).card = S₀.card := by
  simp [decodedMarkedSet]

/-- Decoding a fitting common-window realization recovers the common set
literally. -/
@[simp]
theorem decodedMarkedSet_realizedFinset
    {d N : ℕ} (S : Finset (WindowPlaquette d))
    (hS : ∀ p ∈ S, p.Fits N) :
    decodedMarkedSet (WindowPlaquette.realizedFinset S hS) = S := by
  ext p
  constructor
  · intro hp
    obtain ⟨q, hq, hqp⟩ := Finset.mem_map.mp hp
    obtain ⟨r, hr⟩ :=
      WindowPlaquette.mem_realizedFinset_iff.mp hq
    have hqr : q.toWindow = r.1 := by
      rw [← hr]
      exact WindowPlaquette.toWindow_toConcrete
        r.1 (hS r.1 r.2)
    change q.toWindow = p at hqp
    have hpr : p = r.1 := hqp.symm.trans hqr
    rw [hpr]
    exact r.2
  · intro hp
    apply Finset.mem_map.mpr
    refine ⟨p.toConcrete (hS p hp), ?_, ?_⟩
    · apply WindowPlaquette.mem_realizedFinset_iff.mpr
      exact ⟨⟨p, hp⟩, rfl⟩
    · exact WindowPlaquette.toWindow_toConcrete p (hS p hp)

/-- Every decoded plaquette of a bounded centered marked set fits back in its
source torus. -/
theorem decodedMarkedSet_fits_source
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (R : ℕ)
    (hC : (O.center (R + 2)).minVolume ≤ n)
    (hroom :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    {S₀ : Finset (ConcretePlaquette d (n + 1))}
    (hpin : localNear
      ((O.center (R + 2)).realizedSupport n hC) S₀ = S₀)
    (hcard : S₀.card ≤ R) :
    ∀ p ∈ decodedMarkedSet S₀, p.Fits (n + 1) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hp
  exact ConcretePlaquette.toWindow_fits
    (markedSet_siteMargin_zero O R hC hroom hpin hcard hq)

/-- Every decoded plaquette of the same marked set fits in the target torus. -/
theorem decodedMarkedSet_fits_target
    {d n M : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (R : ℕ)
    (hC : (O.center (R + 2)).minVolume ≤ n)
    (hroomN :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    (hroomM :
      O.minVolume + (R + 2) + 1 + R + 1 < M)
    {S₀ : Finset (ConcretePlaquette d (n + 1))}
    (hpin : localNear
      ((O.center (R + 2)).realizedSupport n hC) S₀ = S₀)
    (hcard : S₀.card ≤ R) :
    ∀ p ∈ decodedMarkedSet S₀, p.Fits M := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hp
  exact markedSet_toWindow_fits_target
    O R hC hroomN hroomM hpin hcard hq

/-- Decoding and re-realizing a bounded centered marked set in the source
volume recovers that set exactly. -/
theorem realizedFinset_decodedMarkedSet_source
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (R : ℕ)
    (hC : (O.center (R + 2)).minVolume ≤ n)
    (hroom :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    {S₀ : Finset (ConcretePlaquette d (n + 1))}
    (hpin : localNear
      ((O.center (R + 2)).realizedSupport n hC) S₀ = S₀)
    (hcard : S₀.card ≤ R) :
    WindowPlaquette.realizedFinset (decodedMarkedSet S₀)
        (decodedMarkedSet_fits_source
          O R hC hroom hpin hcard)
      = S₀ := by
  ext q
  constructor
  · intro hq
    obtain ⟨p, hpq⟩ :=
      WindowPlaquette.mem_realizedFinset_iff.mp hq
    obtain ⟨r, hrS, hrp⟩ := Finset.mem_map.mp p.2
    have hpqWindow :=
      congrArg ConcretePlaquette.toWindow hpq
    simp only [WindowPlaquette.toWindow_toConcrete] at hpqWindow
    have hrqWindow : r.toWindow = q.toWindow :=
      hrp.trans hpqWindow
    have hrq : r = q :=
      ConcretePlaquette.toWindow_injective hrqWindow
    rw [← hrq]
    exact hrS
  · intro hq
    apply WindowPlaquette.mem_realizedFinset_iff.mpr
    refine ⟨⟨q.toWindow, ?_⟩, ?_⟩
    · exact Finset.mem_map.mpr ⟨q, hq, rfl⟩
    · exact ConcretePlaquette.toConcrete_toWindow
        (markedSet_siteMargin_zero
          O R hC hroom hpin hcard hq)

/-- Re-realization of a seam-avoiding marked set in a second torus. -/
noncomputable def transportMarkedSet
    {d n M : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (R : ℕ)
    (hC : (O.center (R + 2)).minVolume ≤ n)
    (hroomN :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    (hroomM :
      O.minVolume + (R + 2) + 1 + R + 1 < M)
    {S₀ : Finset (ConcretePlaquette d (n + 1))}
    (hpin : localNear
      ((O.center (R + 2)).realizedSupport n hC) S₀ = S₀)
    (hcard : S₀.card ≤ R) :
    Finset (ConcretePlaquette d M) :=
  WindowPlaquette.realizedFinset (decodedMarkedSet S₀)
    (decodedMarkedSet_fits_target
      O R hC hroomN hroomM hpin hcard)

@[simp]
theorem decodedMarkedSet_transportMarkedSet
    {d n M : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (R : ℕ)
    (hC : (O.center (R + 2)).minVolume ≤ n)
    (hroomN :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    (hroomM :
      O.minVolume + (R + 2) + 1 + R + 1 < M)
    {S₀ : Finset (ConcretePlaquette d (n + 1))}
    (hpin : localNear
      ((O.center (R + 2)).realizedSupport n hC) S₀ = S₀)
    (hcard : S₀.card ≤ R) :
    decodedMarkedSet
        (transportMarkedSet
          O R hC hroomN hroomM hpin hcard)
      =
    decodedMarkedSet S₀ := by
  unfold transportMarkedSet
  exact decodedMarkedSet_realizedFinset
    (decodedMarkedSet S₀)
    (decodedMarkedSet_fits_target
      O R hC hroomN hroomM hpin hcard)

/-- The transported set still consists exactly of the components meeting
the transported observable support. -/
theorem localNear_transportMarkedSet
    {d n m : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (R : ℕ)
    (hCn : (O.center (R + 2)).minVolume ≤ n)
    (hCm : (O.center (R + 2)).minVolume ≤ m)
    (hroomN :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    (hroomM :
      O.minVolume + (R + 2) + 1 + R + 1 < m + 1)
    {S₀ : Finset (ConcretePlaquette d (n + 1))}
    (hpin : localNear
      ((O.center (R + 2)).realizedSupport n hCn) S₀ = S₀)
    (hcard : S₀.card ≤ R) :
    localNear
        ((O.center (R + 2)).realizedSupport m hCm)
        (transportMarkedSet
          O R hCn hroomN hroomM hpin hcard)
      =
    transportMarkedSet
      O R hCn hroomN hroomM hpin hcard := by
  let C := O.center (R + 2)
  let hSrc := decodedMarkedSet_fits_source
    O R hCn hroomN hpin hcard
  let hTgt := decodedMarkedSet_fits_target
    O R hCn hroomN hroomM hpin hcard
  have hsource :
      localNear
          (WindowPosEdge.realizedFinset C.windowSupport
            (C.windowSupport_fits n hCn))
          (WindowPlaquette.realizedFinset
            (decodedMarkedSet S₀) hSrc)
        =
      WindowPlaquette.realizedFinset
        (decodedMarkedSet S₀) hSrc := by
    rw [C.realizedFinset_windowSupport n hCn,
      realizedFinset_decodedMarkedSet_source
        O R hCn hroomN hpin hcard]
    exact hpin
  have htarget :=
    (localNear_realizedFinset_eq_iff
      C.windowSupport
      (C.windowSupport_fits n hCn)
      (C.windowSupport_fits m hCm)
      (decodedMarkedSet S₀) hSrc hTgt).mp hsource
  change localNear (C.realizedSupport m hCm)
      (transportMarkedSet
        O R hCn hroomN hroomM hpin hcard)
      =
    transportMarkedSet
      O R hCn hroomN hroomM hpin hcard
  rw [← C.realizedFinset_windowSupport m hCm]
  simpa [transportMarkedSet, hTgt] using htarget

@[simp]
theorem card_transportMarkedSet
    {d n M : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (R : ℕ)
    (hC : (O.center (R + 2)).minVolume ≤ n)
    (hroomN :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    (hroomM :
      O.minVolume + (R + 2) + 1 + R + 1 < M)
    {S₀ : Finset (ConcretePlaquette d (n + 1))}
    (hpin : localNear
      ((O.center (R + 2)).realizedSupport n hC) S₀ = S₀)
    (hcard : S₀.card ≤ R) :
    (transportMarkedSet
      O R hC hroomN hroomM hpin hcard).card = S₀.card := by
  rw [transportMarkedSet, WindowPlaquette.card_realizedFinset,
    card_decodedMarkedSet]

/-- Explicit conditions for transporting every centered marked set of
cardinality at most `R`. -/
structure MarkedWindowAdmissible
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (R n : ℕ) : Prop where
  center_le : (O.center (R + 2)).minVolume ≤ n
  room :
    O.minVolume + (R + 2) + 1 + R + 1 < n + 1

/-- Finite index type of complete centered marked sets below the chosen
cardinality bound. -/
def CenteredMarkedSet
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (R n : ℕ)
    (hn : MarkedWindowAdmissible O R n) :=
  {S₀ : Finset (ConcretePlaquette d (n + 1)) //
    localNear
        ((O.center (R + 2)).realizedSupport n hn.center_le) S₀
      = S₀ ∧
    S₀.card ≤ R}

noncomputable instance centeredMarkedSetFintype
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (R n : ℕ)
    (hn : MarkedWindowAdmissible O R n) :
    Fintype (CenteredMarkedSet O R n hn) := by
  classical
  unfold CenteredMarkedSet
  infer_instance

/-- Common-window transport as an element of the target finite marked-set
index type. -/
noncomputable def transportCenteredMarkedSet
    {d n m : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (R : ℕ)
    (hn : MarkedWindowAdmissible O R n)
    (hm : MarkedWindowAdmissible O R m) :
    CenteredMarkedSet O R n hn →
      CenteredMarkedSet O R m hm :=
  fun S₀ => ⟨
    transportMarkedSet
      O R hn.center_le hn.room hm.room S₀.2.1 S₀.2.2,
    localNear_transportMarkedSet
      O R hn.center_le hm.center_le hn.room hm.room
        S₀.2.1 S₀.2.2,
    by
      rw [card_transportMarkedSet]
      exact S₀.2.2⟩

/-- Transport to a second volume and back is literally the identity on
centered marked sets. -/
theorem transportCenteredMarkedSet_leftInverse
    {d n m : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (R : ℕ)
    (hn : MarkedWindowAdmissible O R n)
    (hm : MarkedWindowAdmissible O R m)
    (S₀ : CenteredMarkedSet O R n hn) :
    transportCenteredMarkedSet O R hm hn
        (transportCenteredMarkedSet O R hn hm S₀)
      =
    S₀ := by
  apply Subtype.ext
  let S₁ := transportCenteredMarkedSet O R hn hm S₀
  change
    WindowPlaquette.realizedFinset
        (decodedMarkedSet S₁.1)
        (decodedMarkedSet_fits_target
          O R hm.center_le hm.room hn.room S₁.2.1 S₁.2.2)
      =
    S₀.1
  have hdecode :
      decodedMarkedSet S₁.1 =
      decodedMarkedSet S₀.1 :=
    decodedMarkedSet_transportMarkedSet
      O R hn.center_le hn.room hm.room S₀.2.1 S₀.2.2
  have hsource :=
    realizedFinset_decodedMarkedSet_source
      O R hn.center_le hn.room S₀.2.1 S₀.2.2
  ext q
  constructor
  · intro hq
    obtain ⟨p, hpq⟩ :=
      WindowPlaquette.mem_realizedFinset_iff.mp hq
    rw [← hsource]
    apply WindowPlaquette.mem_realizedFinset_iff.mpr
    refine ⟨⟨p.1, ?_⟩, ?_⟩
    · rw [← hdecode]
      exact p.2
    · exact hpq
  · intro hq
    rw [← hsource] at hq
    obtain ⟨p, hpq⟩ :=
      WindowPlaquette.mem_realizedFinset_iff.mp hq
    apply WindowPlaquette.mem_realizedFinset_iff.mpr
    refine ⟨⟨p.1, ?_⟩, ?_⟩
    · rw [hdecode]
      exact p.2
    · exact hpq

/-- Explicit equivalence of the finite centered marked-set indices in any
two admissible volumes. -/
noncomputable def centeredMarkedSetEquiv
    {d n m : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (R : ℕ)
    (hn : MarkedWindowAdmissible O R n)
    (hm : MarkedWindowAdmissible O R m) :
    CenteredMarkedSet O R n hn ≃
      CenteredMarkedSet O R m hm where
  toFun := transportCenteredMarkedSet O R hn hm
  invFun := transportCenteredMarkedSet O R hm hn
  left_inv := transportCenteredMarkedSet_leftInverse O R hn hm
  right_inv := transportCenteredMarkedSet_leftInverse O R hm hn

/-- The unnormalized marked integral is exactly preserved by common-window
transport.  This statement is deliberately separate from the normalized
cluster correction. -/
theorem integral_center_realize_mul_transportMarkedSet_eq
    {d n m : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G) (R : ℕ)
    (hCn : (O.center (R + 2)).minVolume ≤ n)
    (hCm : (O.center (R + 2)).minVolume ≤ m)
    (hroomN :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    (hroomM :
      O.minVolume + (R + 2) + 1 + R + 1 < m + 1)
    {S₀ : Finset (ConcretePlaquette d (n + 1))}
    (hpin : localNear
      ((O.center (R + 2)).realizedSupport n hCn) S₀ = S₀)
    (hcard : S₀.card ≤ R) :
    (∫ A, (((O.center (R + 2)).realize n A : ℝ) : ℂ) *
        ∏ p ∈ S₀, (plaquetteWeight pe β A p : ℂ)
      ∂(gaugeMeasureFrom (d := d) (N := n + 1) μ))
      =
    ∫ A, (((O.center (R + 2)).realize m A : ℝ) : ℂ) *
        ∏ p ∈ transportMarkedSet
            O R hCn hroomN hroomM hpin hcard,
          (plaquetteWeight pe β A p : ℂ)
      ∂(gaugeMeasureFrom (d := d) (N := m + 1) μ) := by
  have hcross :=
    integral_realize_mul_prod_plaquetteWeight_realizedFinset_eq
      μ pe β (O.center (R + 2)) n m hCn hCm
      (decodedMarkedSet S₀)
      (decodedMarkedSet_fits_source
        O R hCn hroomN hpin hcard)
      (decodedMarkedSet_fits_target
        O R hCn hroomN hroomM hpin hcard)
  rw [realizedFinset_decodedMarkedSet_source
    O R hCn hroomN hpin hcard] at hcross
  simpa [transportMarkedSet] using hcross

end WindowPolymer

end YangMills
