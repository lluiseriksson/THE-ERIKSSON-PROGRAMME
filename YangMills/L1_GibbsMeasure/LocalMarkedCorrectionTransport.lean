/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.L1_GibbsMeasure.LocalMarkedTransport

/-!
# Joint transport of a marked set and its normalization clusters

The normalized marked term is pinned to the union of the observable support
and the plaquette-edge support of the marked set.  This module constructs the
common-window representative of every below-cutoff correction cluster
meeting that combined support.
-/

namespace YangMills

open MeasureTheory GaugeConfig

namespace WindowPolymer

open Classical

/-- Realization commutes with union of two fitting common-window edge
sets. -/
theorem WindowPosEdge.realizedFinset_union
    {d N : ℕ}
    (U V : Finset (WindowPosEdge d))
    (hUV : ∀ e ∈ U ∪ V, e.Fits N)
    (hU : ∀ e ∈ U, e.Fits N)
    (hV : ∀ e ∈ V, e.Fits N) :
    WindowPosEdge.realizedFinset (U ∪ V) hUV
      =
    WindowPosEdge.realizedFinset U hU ∪
      WindowPosEdge.realizedFinset V hV := by
  ext q
  constructor
  · intro hq
    obtain ⟨e, heq⟩ :=
      WindowPosEdge.mem_realizedFinset_iff.mp hq
    rcases Finset.mem_union.mp e.2 with heU | heV
    · apply Finset.mem_union_left
      apply WindowPosEdge.mem_realizedFinset_iff.mpr
      exact ⟨⟨e.1, heU⟩, by simpa using heq⟩
    · apply Finset.mem_union_right
      apply WindowPosEdge.mem_realizedFinset_iff.mpr
      exact ⟨⟨e.1, heV⟩, by simpa using heq⟩
  · intro hq
    rcases Finset.mem_union.mp hq with hqU | hqV
    · obtain ⟨e, heq⟩ :=
        WindowPosEdge.mem_realizedFinset_iff.mp hqU
      apply WindowPosEdge.mem_realizedFinset_iff.mpr
      refine ⟨⟨e.1, Finset.mem_union_left V e.2⟩, ?_⟩
      simpa using heq
    · obtain ⟨e, heq⟩ :=
        WindowPosEdge.mem_realizedFinset_iff.mp hqV
      apply WindowPosEdge.mem_realizedFinset_iff.mpr
      refine ⟨⟨e.1, Finset.mem_union_right U e.2⟩, ?_⟩
      simpa using heq

/-- Common-window edge support which pins the normalized correction for a
marked set. -/
noncomputable def combinedWindowSupport
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (C : CompatibleLocalObservable d G)
    (S : Finset (WindowPlaquette d)) :
    Finset (WindowPosEdge d) :=
  C.windowSupport ∪ WindowPlaquette.edgeSupport S

/-- The combined support fits whenever both constituent window supports
fit. -/
theorem combinedWindowSupport_fits
    {d N : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (C : CompatibleLocalObservable d G)
    (S : Finset (WindowPlaquette d))
    (hC : ∀ e ∈ C.windowSupport, e.Fits N)
    (hS : ∀ p ∈ S, p.Fits N) :
    ∀ e ∈ combinedWindowSupport C S, e.Fits N := by
  intro e he
  rcases Finset.mem_union.mp he with heC | heS
  · exact hC e heC
  · exact WindowPlaquette.edgeSupport_fits hS e heS

/-- Realizing the combined common-window support gives exactly the union
which appears in the finite-volume normalized marked term. -/
theorem realizedFinset_combinedWindowSupport
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (C : CompatibleLocalObservable d G)
    (hn : C.minVolume ≤ n)
    (S : Finset (WindowPlaquette d))
    (hS : ∀ p ∈ S, p.Fits (n + 1)) :
    WindowPosEdge.realizedFinset
        (combinedWindowSupport C S)
        (combinedWindowSupport_fits
          C S (C.windowSupport_fits n hn) hS)
      =
    C.realizedSupport n hn ∪
      (WindowPlaquette.realizedFinset S hS).biUnion
        plaquetteSupport := by
  change
    WindowPosEdge.realizedFinset
        (C.windowSupport ∪ WindowPlaquette.edgeSupport S)
        (combinedWindowSupport_fits
          C S (C.windowSupport_fits n hn) hS)
      =
    C.realizedSupport n hn ∪
      (WindowPlaquette.realizedFinset S hS).biUnion
        plaquetteSupport
  rw [WindowPosEdge.realizedFinset_union
      C.windowSupport (WindowPlaquette.edgeSupport S)
      (combinedWindowSupport_fits
        C S (C.windowSupport_fits n hn) hS)
      (C.windowSupport_fits n hn)
      (WindowPlaquette.edgeSupport_fits hS),
    C.realizedFinset_windowSupport n hn,
    WindowPlaquette.biUnion_support_realizedFinset hS]

/-- A below-cutoff cluster meeting the combined support of a centered
observable and a small complete marked set has one common-window
representative fitting in both volumes. -/
theorem exists_commonWindow_of_smallCluster_unionMarkedSupport
    {d n m k : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (R K L : ℕ)
    (hCn : (O.center (R + 2)).minVolume ≤ n)
    (hroomN :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    (hroomM :
      O.minVolume + (R + 2) + 1 + R + 1 < m + 1)
    {S₀ : Finset (ConcretePlaquette d (n + 1))}
    (hpin : localNear
      ((O.center (R + 2)).realizedSupport n hCn) S₀ = S₀)
    (hcard : S₀.card ≤ K)
    (hres : (2 * L + 1) + K ≤ R)
    {X : Fin k →
      (connectedLatticePolymerSystem
        (d := d) (N := n + 1) μ pe β).Polymer}
    (hX : KP.IsCluster
      (connectedLatticePolymerSystem
        (d := d) (N := n + 1) μ pe β) X)
    (hmeet : ∃ i, ¬ Disjoint (X i).1
      (supportPlaquettes
        (((O.center (R + 2)).realizedSupport n hCn) ∪
          S₀.biUnion plaquetteSupport)))
    (hsmall : (∑ i, (X i).1.card) < L) :
    ∃ Y : Fin k → WindowPolymer d,
      ∃ hYn : ∀ j, (Y j).Fits (n + 1),
      ∃ _hYm : ∀ j, (Y j).Fits (m + 1),
      ∀ j,
        (Y j).toWeightedPolymer μ
          (wilsonPlaquetteWeight pe β) (hYn j) = X j := by
  obtain ⟨i₀, hi₀⟩ := hmeet
  obtain ⟨p, hpX, hpS⟩ :=
    Finset.not_disjoint_iff.mp hi₀
  have hpMarginLarge : p.SiteMargin (2 * L) :=
    unionMarkedSupport_siteMargin
      O R K L hCn hroomN hpin hcard hres hpS
  have hsize :
      2 * ∑ i, (X i).1.card ≤ 2 * L := by
    omega
  have hpMargin :
      p.SiteMargin (2 * ∑ i, (X i).1.card) :=
    hpMarginLarge.mono hsize
  let Y := decodedClusterTuple μ
    (wilsonPlaquetteWeight pe β) hX hpX hpMargin
  have hYn : ∀ j, (Y j).Fits (n + 1) :=
    decodedClusterTuple_fits_source μ
      (wilsonPlaquetteWeight pe β) hX hpX hpMargin
  have hpTargetLarge :
      ∀ j, (p.site j).val + 2 * L + 1 < m + 1 :=
    unionMarkedSupport_targetRoom
      O R K L hCn hroomN hroomM
        hpin hcard hres hpS
  have hpTarget :
      ∀ j,
        (p.site j).val +
            (2 * ∑ i, (X i).1.card) + 1
          < m + 1 := by
    intro j
    have hj := hpTargetLarge j
    omega
  have hYm : ∀ j, (Y j).Fits (m + 1) :=
    decodedClusterTuple_fits_target μ
      (wilsonPlaquetteWeight pe β) hX hpX hpMargin hpTarget
  refine ⟨Y, hYn, hYm, ?_⟩
  intro j
  exact toWeightedPolymer_decodedClusterTuple μ
    (wilsonPlaquetteWeight pe β) hX hpX hpMargin j

/-- Connected below-cutoff correction tuples pinned to the combined support
of one fixed marked set. -/
def CombinedSmallClusterTuple
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (R L : ℕ)
    (hC : (O.center (R + 2)).minVolume ≤ n)
    (S₀ : Finset (ConcretePlaquette d (n + 1)))
    (k : ℕ) :=
  {X : Fin k →
      (connectedLatticePolymerSystem
        (d := d) (N := n + 1) μ pe β).Polymer //
    KP.IsCluster
        (connectedLatticePolymerSystem
          (d := d) (N := n + 1) μ pe β) X ∧
      (∃ i, ¬ Disjoint (X i).1
        (supportPlaquettes
          (((O.center (R + 2)).realizedSupport n hC) ∪
            S₀.biUnion plaquetteSupport))) ∧
      (∑ i, (X i).1.card) < L}

noncomputable instance combinedSmallClusterTupleFintype
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (R L : ℕ)
    (hC : (O.center (R + 2)).minVolume ≤ n)
    (S₀ : Finset (ConcretePlaquette d (n + 1)))
    (k : ℕ) :
    Fintype
      (CombinedSmallClusterTuple μ pe β O R L hC S₀ k) := by
  classical
  unfold CombinedSmallClusterTuple
  infer_instance

/-- Canonical common-window representative of a combined-support
below-cutoff correction tuple. -/
noncomputable def combinedSmallClusterCommonWindow
    {d n m k : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (R K L : ℕ)
    (hCn : (O.center (R + 2)).minVolume ≤ n)
    (hroomN :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    (hroomM :
      O.minVolume + (R + 2) + 1 + R + 1 < m + 1)
    {S₀ : Finset (ConcretePlaquette d (n + 1))}
    (hpin : localNear
      ((O.center (R + 2)).realizedSupport n hCn) S₀ = S₀)
    (hcard : S₀.card ≤ K)
    (hres : (2 * L + 1) + K ≤ R)
    (X : CombinedSmallClusterTuple
      μ pe β O R L hCn S₀ k) :
    CommonWindowTuple (m := m) μ pe β X.1 := by
  classical
  let hex :=
    exists_commonWindow_of_smallCluster_unionMarkedSupport
      μ pe β O R K L hCn hroomN hroomM
        hpin hcard hres X.2.1 X.2.2.1 X.2.2.2
  let Y := Classical.choose hex
  let hrest := Classical.choose_spec hex
  let hYn := Classical.choose hrest
  let hrest' := Classical.choose_spec hrest
  let hYm := Classical.choose hrest'
  let hsource := Classical.choose_spec hrest'
  exact ⟨Y, hYn, hYm, hsource⟩

/-- Target realization of the canonical combined-support tuple. -/
noncomputable def combinedSmallClusterTargetTuple
    {d n m k : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (R K L : ℕ)
    (hCn : (O.center (R + 2)).minVolume ≤ n)
    (hroomN :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    (hroomM :
      O.minVolume + (R + 2) + 1 + R + 1 < m + 1)
    {S₀ : Finset (ConcretePlaquette d (n + 1))}
    (hpin : localNear
      ((O.center (R + 2)).realizedSupport n hCn) S₀ = S₀)
    (hcard : S₀.card ≤ K)
    (hres : (2 * L + 1) + K ≤ R)
    (X : CombinedSmallClusterTuple
      μ pe β O R L hCn S₀ k) :
    Fin k →
      (connectedLatticePolymerSystem
        (d := d) (N := m + 1) μ pe β).Polymer :=
  let W := combinedSmallClusterCommonWindow
    μ pe β O R K L hCn hroomN hroomM
      hpin hcard hres X
  fun j => (W.tuple j).toWeightedPolymer μ
    (wilsonPlaquetteWeight pe β) (W.targetFits j)

/-- Target realization preserves the total plaquette cardinality. -/
theorem sum_card_combinedSmallClusterTargetTuple
    {d n m k : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (R K L : ℕ)
    (hCn : (O.center (R + 2)).minVolume ≤ n)
    (hroomN :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    (hroomM :
      O.minVolume + (R + 2) + 1 + R + 1 < m + 1)
    {S₀ : Finset (ConcretePlaquette d (n + 1))}
    (hpin : localNear
      ((O.center (R + 2)).realizedSupport n hCn) S₀ = S₀)
    (hcard : S₀.card ≤ K)
    (hres : (2 * L + 1) + K ≤ R)
    (X : CombinedSmallClusterTuple
      μ pe β O R L hCn S₀ k) :
    (∑ i, (combinedSmallClusterTargetTuple
      μ pe β O R K L hCn hroomN hroomM
        hpin hcard hres X i).1.card)
      =
    ∑ i, (X.1 i).1.card := by
  let W := combinedSmallClusterCommonWindow
    μ pe β O R K L hCn hroomN hroomM
      hpin hcard hres X
  calc
    (∑ i, (combinedSmallClusterTargetTuple
        μ pe β O R K L hCn hroomN hroomM
          hpin hcard hres X i).1.card)
        = ∑ i, (W.tuple i).support.card := by
          apply Finset.sum_congr rfl
          intro i _
          exact card_toWeightedPolymer μ
            (wilsonPlaquetteWeight pe β)
            (W.tuple i) (W.targetFits i)
    _ = ∑ i, (X.1 i).1.card := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← W.source_eq i]
          exact (card_toWeightedPolymer μ
            (wilsonPlaquetteWeight pe β)
            (W.tuple i) (W.sourceFits i)).symm

/-- The target tuple remains a connected cluster. -/
theorem isCluster_combinedSmallClusterTargetTuple
    {d n m k : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (R K L : ℕ)
    (hCn : (O.center (R + 2)).minVolume ≤ n)
    (hroomN :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    (hroomM :
      O.minVolume + (R + 2) + 1 + R + 1 < m + 1)
    {S₀ : Finset (ConcretePlaquette d (n + 1))}
    (hpin : localNear
      ((O.center (R + 2)).realizedSupport n hCn) S₀ = S₀)
    (hcard : S₀.card ≤ K)
    (hres : (2 * L + 1) + K ≤ R)
    (X : CombinedSmallClusterTuple
      μ pe β O R L hCn S₀ k) :
    KP.IsCluster
      (connectedLatticePolymerSystem
        (d := d) (N := m + 1) μ pe β)
      (combinedSmallClusterTargetTuple
        μ pe β O R K L hCn hroomN hroomM
          hpin hcard hres X) := by
  let W := combinedSmallClusterCommonWindow
    μ pe β O R K L hCn hroomN hroomM
      hpin hcard hres X
  have hiff := isCluster_toWeightedPolymer_iff μ
    (wilsonPlaquetteWeight pe β)
    (wilsonPlaquetteWeight pe β)
    W.tuple W.sourceFits W.targetFits
  apply hiff.mp
  have htuple :
      (fun j => (W.tuple j).toWeightedPolymer μ
        (wilsonPlaquetteWeight pe β) (W.sourceFits j))
        = X.1 :=
    funext W.source_eq
  rw [htuple]
  exact X.2.1

/-- Incidence with the full combined pinning support is transported
exactly. -/
theorem meets_combinedSmallClusterTargetTuple
    {d n m k : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (R K L : ℕ)
    (hCn : (O.center (R + 2)).minVolume ≤ n)
    (hCm : (O.center (R + 2)).minVolume ≤ m)
    (hroomN :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    (hroomM :
      O.minVolume + (R + 2) + 1 + R + 1 < m + 1)
    {S₀ : Finset (ConcretePlaquette d (n + 1))}
    (hpin : localNear
      ((O.center (R + 2)).realizedSupport n hCn) S₀ = S₀)
    (hcard : S₀.card ≤ K)
    (hres : (2 * L + 1) + K ≤ R)
    (X : CombinedSmallClusterTuple
      μ pe β O R L hCn S₀ k) :
    ∃ i, ¬ Disjoint
      (combinedSmallClusterTargetTuple
        μ pe β O R K L hCn hroomN hroomM
          hpin hcard hres X i).1
      (supportPlaquettes
        (((O.center (R + 2)).realizedSupport m hCm) ∪
          (transportMarkedSet
            O R hCn hroomN hroomM hpin
              (hcard.trans (by omega))).biUnion
            plaquetteSupport)) := by
  let C := O.center (R + 2)
  let S := decodedMarkedSet S₀
  let hSn := decodedMarkedSet_fits_source
    O R hCn hroomN hpin (hcard.trans (by omega))
  let hSm := decodedMarkedSet_fits_target
    O R hCn hroomN hroomM hpin (hcard.trans (by omega))
  let U := combinedWindowSupport C S
  let uN := combinedWindowSupport_fits
    C S (C.windowSupport_fits n hCn) hSn
  let uM := combinedWindowSupport_fits
    C S (C.windowSupport_fits m hCm) hSm
  let W := combinedSmallClusterCommonWindow
    μ pe β O R K L hCn hroomN hroomM
      hpin hcard hres X
  obtain ⟨i, hi⟩ := X.2.2.1
  obtain ⟨p, hpXi, hpS⟩ :=
    Finset.not_disjoint_iff.mp hi
  have hpWi : p ∈
      ((W.tuple i).toWeightedPolymer μ
        (wilsonPlaquetteWeight pe β) (W.sourceFits i)).1 := by
    rw [W.source_eq i]
    exact hpXi
  rw [toWeightedPolymer_val] at hpWi
  obtain ⟨q, hqp⟩ :=
    WindowPlaquette.mem_realizedFinset_iff.mp hpWi
  have hqSource :
      q.1.toConcrete (W.sourceFits i q.1 q.2) ∈
        supportPlaquettes
          (WindowPosEdge.realizedFinset U uN) := by
    rw [realizedFinset_combinedWindowSupport
      C hCn S hSn]
    rw [realizedFinset_decodedMarkedSet_source
      O R hCn hroomN hpin (hcard.trans (by omega))]
    simpa [hqp] using hpS
  have hqTarget :=
    (WindowPlaquette.mem_supportPlaquettes_realizedFinset_iff
      U uN uM q.1
      (W.sourceFits i q.1 q.2)
      (W.targetFits i q.1 q.2)).mp hqSource
  refine ⟨i, Finset.not_disjoint_iff.mpr ?_⟩
  refine ⟨q.1.toConcrete (W.targetFits i q.1 q.2), ?_, ?_⟩
  · change q.1.toConcrete (W.targetFits i q.1 q.2) ∈
      ((W.tuple i).toWeightedPolymer μ
        (wilsonPlaquetteWeight pe β) (W.targetFits i)).1
    rw [toWeightedPolymer_val]
    apply WindowPlaquette.mem_realizedFinset_iff.mpr
    exact ⟨q, rfl⟩
  · rw [realizedFinset_combinedWindowSupport
      C hCm S hSm] at hqTarget
    simpa [C, S, hSm, transportMarkedSet] using hqTarget

/-- The same combined-support tuple type, indexed directly by its
volume-independent marked window.  This is the form whose source and target
types compose literally under transport. -/
abbrev CommonCombinedSmallClusterTuple
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (R L : ℕ)
    (hC : (O.center (R + 2)).minVolume ≤ n)
    (S : Finset (WindowPlaquette d))
    (hS : ∀ p ∈ S, p.Fits (n + 1))
    (k : ℕ) :=
  CombinedSmallClusterTuple μ pe β O R L hC
    (WindowPlaquette.realizedFinset S hS) k

/-- Canonical representative for the common-marked-window tuple type. -/
noncomputable def commonCombinedSmallClusterWindow
    {d n m k : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (R K L : ℕ)
    (hCn : (O.center (R + 2)).minVolume ≤ n)
    (hroomN :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    (hroomM :
      O.minVolume + (R + 2) + 1 + R + 1 < m + 1)
    (S : Finset (WindowPlaquette d))
    (hSn : ∀ p ∈ S, p.Fits (n + 1))
    (hSm : ∀ p ∈ S, p.Fits (m + 1))
    (hnearN : localNear
      ((O.center (R + 2)).realizedSupport n hCn)
      (WindowPlaquette.realizedFinset S hSn)
        =
      WindowPlaquette.realizedFinset S hSn)
    (hcardS : S.card ≤ K)
    (hres : (2 * L + 1) + K ≤ R)
    (X : CommonCombinedSmallClusterTuple
      μ pe β O R L hCn S hSn k) :
    CommonWindowTuple (m := m) μ pe β X.1 := by
  apply combinedSmallClusterCommonWindow
    μ pe β O R K L hCn hroomN hroomM
      hnearN
  · rw [WindowPlaquette.card_realizedFinset hSn]
    exact hcardS
  · exact hres

/-- Target realization for the common-marked-window tuple type. -/
noncomputable def commonCombinedSmallClusterTargetTuple
    {d n m k : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (R K L : ℕ)
    (hCn : (O.center (R + 2)).minVolume ≤ n)
    (hroomN :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    (hroomM :
      O.minVolume + (R + 2) + 1 + R + 1 < m + 1)
    (S : Finset (WindowPlaquette d))
    (hSn : ∀ p ∈ S, p.Fits (n + 1))
    (hSm : ∀ p ∈ S, p.Fits (m + 1))
    (hnearN : localNear
      ((O.center (R + 2)).realizedSupport n hCn)
      (WindowPlaquette.realizedFinset S hSn)
        =
      WindowPlaquette.realizedFinset S hSn)
    (hcardS : S.card ≤ K)
    (hres : (2 * L + 1) + K ≤ R)
    (X : CommonCombinedSmallClusterTuple
      μ pe β O R L hCn S hSn k) :
    Fin k →
      (connectedLatticePolymerSystem
        (d := d) (N := m + 1) μ pe β).Polymer :=
  let W := commonCombinedSmallClusterWindow
    μ pe β O R K L hCn hroomN hroomM
      S hSn hSm hnearN hcardS hres X
  fun j => (W.tuple j).toWeightedPolymer μ
    (wilsonPlaquetteWeight pe β) (W.targetFits j)

/-- The common-window target tuple preserves its total size. -/
theorem sum_card_commonCombinedSmallClusterTargetTuple
    {d n m k : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (R K L : ℕ)
    (hCn : (O.center (R + 2)).minVolume ≤ n)
    (hroomN :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    (hroomM :
      O.minVolume + (R + 2) + 1 + R + 1 < m + 1)
    (S : Finset (WindowPlaquette d))
    (hSn : ∀ p ∈ S, p.Fits (n + 1))
    (hSm : ∀ p ∈ S, p.Fits (m + 1))
    (hnearN : localNear
      ((O.center (R + 2)).realizedSupport n hCn)
      (WindowPlaquette.realizedFinset S hSn)
        =
      WindowPlaquette.realizedFinset S hSn)
    (hcardS : S.card ≤ K)
    (hres : (2 * L + 1) + K ≤ R)
    (X : CommonCombinedSmallClusterTuple
      μ pe β O R L hCn S hSn k) :
    (∑ i, (commonCombinedSmallClusterTargetTuple
      μ pe β O R K L hCn hroomN hroomM
        S hSn hSm hnearN hcardS hres X i).1.card)
      =
    ∑ i, (X.1 i).1.card := by
  let W := commonCombinedSmallClusterWindow
    μ pe β O R K L hCn hroomN hroomM
      S hSn hSm hnearN hcardS hres X
  calc
    (∑ i, (commonCombinedSmallClusterTargetTuple
        μ pe β O R K L hCn hroomN hroomM
          S hSn hSm hnearN hcardS hres X i).1.card)
        = ∑ i, (W.tuple i).support.card := by
          apply Finset.sum_congr rfl
          intro i _
          exact card_toWeightedPolymer μ
            (wilsonPlaquetteWeight pe β)
            (W.tuple i) (W.targetFits i)
    _ = ∑ i, (X.1 i).1.card := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← W.source_eq i]
          exact (card_toWeightedPolymer μ
            (wilsonPlaquetteWeight pe β)
            (W.tuple i) (W.sourceFits i)).symm

/-- The common-window target tuple is still a connected cluster. -/
theorem isCluster_commonCombinedSmallClusterTargetTuple
    {d n m k : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (R K L : ℕ)
    (hCn : (O.center (R + 2)).minVolume ≤ n)
    (hroomN :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    (hroomM :
      O.minVolume + (R + 2) + 1 + R + 1 < m + 1)
    (S : Finset (WindowPlaquette d))
    (hSn : ∀ p ∈ S, p.Fits (n + 1))
    (hSm : ∀ p ∈ S, p.Fits (m + 1))
    (hnearN : localNear
      ((O.center (R + 2)).realizedSupport n hCn)
      (WindowPlaquette.realizedFinset S hSn)
        =
      WindowPlaquette.realizedFinset S hSn)
    (hcardS : S.card ≤ K)
    (hres : (2 * L + 1) + K ≤ R)
    (X : CommonCombinedSmallClusterTuple
      μ pe β O R L hCn S hSn k) :
    KP.IsCluster
      (connectedLatticePolymerSystem
        (d := d) (N := m + 1) μ pe β)
      (commonCombinedSmallClusterTargetTuple
        μ pe β O R K L hCn hroomN hroomM
          S hSn hSm hnearN hcardS hres X) := by
  let W := commonCombinedSmallClusterWindow
    μ pe β O R K L hCn hroomN hroomM
      S hSn hSm hnearN hcardS hres X
  have hiff := isCluster_toWeightedPolymer_iff μ
    (wilsonPlaquetteWeight pe β)
    (wilsonPlaquetteWeight pe β)
    W.tuple W.sourceFits W.targetFits
  apply hiff.mp
  have htuple :
      (fun j => (W.tuple j).toWeightedPolymer μ
        (wilsonPlaquetteWeight pe β) (W.sourceFits j))
        = X.1 :=
    funext W.source_eq
  rw [htuple]
  exact X.2.1

/-- Combined-support incidence for the common marked window is transported
exactly. -/
theorem meets_commonCombinedSmallClusterTargetTuple
    {d n m k : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (R K L : ℕ)
    (hCn : (O.center (R + 2)).minVolume ≤ n)
    (hCm : (O.center (R + 2)).minVolume ≤ m)
    (hroomN :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    (hroomM :
      O.minVolume + (R + 2) + 1 + R + 1 < m + 1)
    (S : Finset (WindowPlaquette d))
    (hSn : ∀ p ∈ S, p.Fits (n + 1))
    (hSm : ∀ p ∈ S, p.Fits (m + 1))
    (hnearN : localNear
      ((O.center (R + 2)).realizedSupport n hCn)
      (WindowPlaquette.realizedFinset S hSn)
        =
      WindowPlaquette.realizedFinset S hSn)
    (hcardS : S.card ≤ K)
    (hres : (2 * L + 1) + K ≤ R)
    (X : CommonCombinedSmallClusterTuple
      μ pe β O R L hCn S hSn k) :
    ∃ i, ¬ Disjoint
      (commonCombinedSmallClusterTargetTuple
        μ pe β O R K L hCn hroomN hroomM
          S hSn hSm hnearN hcardS hres X i).1
      (supportPlaquettes
        (((O.center (R + 2)).realizedSupport m hCm) ∪
          (WindowPlaquette.realizedFinset S hSm).biUnion
            plaquetteSupport)) := by
  let C := O.center (R + 2)
  let U := combinedWindowSupport C S
  let uN := combinedWindowSupport_fits
    C S (C.windowSupport_fits n hCn) hSn
  let uM := combinedWindowSupport_fits
    C S (C.windowSupport_fits m hCm) hSm
  let W := commonCombinedSmallClusterWindow
    μ pe β O R K L hCn hroomN hroomM
      S hSn hSm hnearN hcardS hres X
  obtain ⟨i, hi⟩ := X.2.2.1
  obtain ⟨p, hpXi, hpS⟩ :=
    Finset.not_disjoint_iff.mp hi
  have hpWi : p ∈
      ((W.tuple i).toWeightedPolymer μ
        (wilsonPlaquetteWeight pe β) (W.sourceFits i)).1 := by
    rw [W.source_eq i]
    exact hpXi
  rw [toWeightedPolymer_val] at hpWi
  obtain ⟨q, hqp⟩ :=
    WindowPlaquette.mem_realizedFinset_iff.mp hpWi
  have hqSource :
      q.1.toConcrete (W.sourceFits i q.1 q.2) ∈
        supportPlaquettes
          (WindowPosEdge.realizedFinset U uN) := by
    rw [realizedFinset_combinedWindowSupport C hCn S hSn]
    simpa [hqp] using hpS
  have hqTarget :=
    (WindowPlaquette.mem_supportPlaquettes_realizedFinset_iff
      U uN uM q.1
      (W.sourceFits i q.1 q.2)
      (W.targetFits i q.1 q.2)).mp hqSource
  refine ⟨i, Finset.not_disjoint_iff.mpr ?_⟩
  refine ⟨q.1.toConcrete (W.targetFits i q.1 q.2), ?_, ?_⟩
  · change q.1.toConcrete (W.targetFits i q.1 q.2) ∈
      ((W.tuple i).toWeightedPolymer μ
        (wilsonPlaquetteWeight pe β) (W.targetFits i)).1
    rw [toWeightedPolymer_val]
    apply WindowPlaquette.mem_realizedFinset_iff.mpr
    exact ⟨q, rfl⟩
  · rw [realizedFinset_combinedWindowSupport C hCm S hSm]
        at hqTarget
    exact hqTarget

/-- Complete-near status of a common marked window is equivalent in every
two fitting admissible volumes. -/
theorem localNear_commonMarkedWindow_iff
    {d n m : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (C : CompatibleLocalObservable d G)
    (hn : C.minVolume ≤ n) (hm : C.minVolume ≤ m)
    (S : Finset (WindowPlaquette d))
    (hSn : ∀ p ∈ S, p.Fits (n + 1))
    (hSm : ∀ p ∈ S, p.Fits (m + 1)) :
    localNear (C.realizedSupport n hn)
        (WindowPlaquette.realizedFinset S hSn)
        =
      WindowPlaquette.realizedFinset S hSn
      ↔
    localNear (C.realizedSupport m hm)
        (WindowPlaquette.realizedFinset S hSm)
        =
      WindowPlaquette.realizedFinset S hSm := by
  rw [← C.realizedFinset_windowSupport n hn,
    ← C.realizedFinset_windowSupport m hm]
  exact localNear_realizedFinset_eq_iff
    C.windowSupport
      (C.windowSupport_fits n hn)
      (C.windowSupport_fits m hm)
      S hSn hSm

/-- Transport of a common-window combined-support tuple as an element of
the target finite index type. -/
noncomputable def transportCommonCombinedSmallCluster
    {d n m k : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (R K L : ℕ)
    (hCn : (O.center (R + 2)).minVolume ≤ n)
    (hCm : (O.center (R + 2)).minVolume ≤ m)
    (hroomN :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    (hroomM :
      O.minVolume + (R + 2) + 1 + R + 1 < m + 1)
    (S : Finset (WindowPlaquette d))
    (hSn : ∀ p ∈ S, p.Fits (n + 1))
    (hSm : ∀ p ∈ S, p.Fits (m + 1))
    (hnearN : localNear
      ((O.center (R + 2)).realizedSupport n hCn)
      (WindowPlaquette.realizedFinset S hSn)
        =
      WindowPlaquette.realizedFinset S hSn)
    (hcardS : S.card ≤ K)
    (hres : (2 * L + 1) + K ≤ R) :
    CommonCombinedSmallClusterTuple
        μ pe β O R L hCn S hSn k →
      CommonCombinedSmallClusterTuple
        μ pe β O R L hCm S hSm k :=
  fun X => ⟨
    commonCombinedSmallClusterTargetTuple
      μ pe β O R K L hCn hroomN hroomM
        S hSn hSm hnearN hcardS hres X,
    isCluster_commonCombinedSmallClusterTargetTuple
      μ pe β O R K L hCn hroomN hroomM
        S hSn hSm hnearN hcardS hres X,
    meets_commonCombinedSmallClusterTargetTuple
      μ pe β O R K L hCn hCm hroomN hroomM
        S hSn hSm hnearN hcardS hres X,
    by
      rw [sum_card_commonCombinedSmallClusterTargetTuple
        μ pe β O R K L hCn hroomN hroomM
          S hSn hSm hnearN hcardS hres X]
      exact X.2.2.2⟩

/-- The full Ursell/activity monomial is unchanged by joint transport. -/
theorem weightedClusterMonomial_transportCommonCombinedSmallCluster
    {d n m k : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (R K L : ℕ)
    (hCn : (O.center (R + 2)).minVolume ≤ n)
    (hCm : (O.center (R + 2)).minVolume ≤ m)
    (hroomN :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    (hroomM :
      O.minVolume + (R + 2) + 1 + R + 1 < m + 1)
    (S : Finset (WindowPlaquette d))
    (hSn : ∀ p ∈ S, p.Fits (n + 1))
    (hSm : ∀ p ∈ S, p.Fits (m + 1))
    (hnearN : localNear
      ((O.center (R + 2)).realizedSupport n hCn)
      (WindowPlaquette.realizedFinset S hSn)
        =
      WindowPlaquette.realizedFinset S hSn)
    (hcardS : S.card ≤ K)
    (hres : (2 * L + 1) + K ≤ R)
    (X : CommonCombinedSmallClusterTuple
      μ pe β O R L hCn S hSn k) :
    weightedClusterMonomial μ
        (wilsonPlaquetteWeight pe β) X.1
      =
    weightedClusterMonomial μ
      (wilsonPlaquetteWeight pe β)
      (transportCommonCombinedSmallCluster
        μ pe β O R K L hCn hCm hroomN hroomM
          S hSn hSm hnearN hcardS hres X).1 := by
  let W := commonCombinedSmallClusterWindow
    μ pe β O R K L hCn hroomN hroomM
      S hSn hSm hnearN hcardS hres X
  exact weightedClusterMonomial_eq_of_commonWindow
    μ pe β X.1 W.tuple W.sourceFits W.targetFits W.source_eq

/-- Joint transport to a second volume and back is literally the identity
on common-window correction tuples. -/
theorem transportCommonCombinedSmallCluster_leftInverse
    {d n m k : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (R K L : ℕ)
    (hCn : (O.center (R + 2)).minVolume ≤ n)
    (hCm : (O.center (R + 2)).minVolume ≤ m)
    (hroomN :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    (hroomM :
      O.minVolume + (R + 2) + 1 + R + 1 < m + 1)
    (S : Finset (WindowPlaquette d))
    (hSn : ∀ p ∈ S, p.Fits (n + 1))
    (hSm : ∀ p ∈ S, p.Fits (m + 1))
    (hnearN : localNear
      ((O.center (R + 2)).realizedSupport n hCn)
      (WindowPlaquette.realizedFinset S hSn)
        =
      WindowPlaquette.realizedFinset S hSn)
    (hcardS : S.card ≤ K)
    (hres : (2 * L + 1) + K ≤ R)
    (X : CommonCombinedSmallClusterTuple
      μ pe β O R L hCn S hSn k) :
    let hnearM :=
      (localNear_commonMarkedWindow_iff
        (O.center (R + 2)) hCn hCm S hSn hSm).mp hnearN
    transportCommonCombinedSmallCluster
        μ pe β O R K L hCm hCn hroomM hroomN
          S hSm hSn hnearM hcardS hres
      (transportCommonCombinedSmallCluster
        μ pe β O R K L hCn hCm hroomN hroomM
          S hSn hSm hnearN hcardS hres X)
      =
    X := by
  dsimp only
  apply Subtype.ext
  funext j
  let hnearM :=
    (localNear_commonMarkedWindow_iff
      (O.center (R + 2)) hCn hCm S hSn hSm).mp hnearN
  let W := commonCombinedSmallClusterWindow
    μ pe β O R K L hCn hroomN hroomM
      S hSn hSm hnearN hcardS hres X
  let X' := transportCommonCombinedSmallCluster
    μ pe β O R K L hCn hCm hroomN hroomM
      S hSn hSm hnearN hcardS hres X
  let V := commonCombinedSmallClusterWindow
    μ pe β O R K L hCm hroomM hroomN
      S hSm hSn hnearM hcardS hres X'
  have hreal :
      (V.tuple j).toWeightedPolymer μ
          (wilsonPlaquetteWeight pe β) (V.sourceFits j)
        =
      (W.tuple j).toWeightedPolymer μ
          (wilsonPlaquetteWeight pe β) (W.targetFits j) := by
    have htarget :
        X'.1 j =
          (W.tuple j).toWeightedPolymer μ
            (wilsonPlaquetteWeight pe β) (W.targetFits j) := by
      change commonCombinedSmallClusterTargetTuple
        μ pe β O R K L hCn hroomN hroomM
          S hSn hSm hnearN hcardS hres X j
        =
          (W.tuple j).toWeightedPolymer μ
            (wilsonPlaquetteWeight pe β) (W.targetFits j)
      rfl
    exact (V.source_eq j).trans htarget
  have hVW : V.tuple j = W.tuple j :=
    toWeightedPolymer_injective_of_fits μ
      (wilsonPlaquetteWeight pe β)
      (V.sourceFits j) (W.targetFits j) hreal
  change
    (V.tuple j).toWeightedPolymer μ
        (wilsonPlaquetteWeight pe β) (V.targetFits j)
      =
    X.1 j
  exact (toWeightedPolymer_congr μ
    (wilsonPlaquetteWeight pe β)
    (V.targetFits j) (W.sourceFits j) hVW).trans
      (W.source_eq j)

/-- Explicit equivalence of every finite joint below-cutoff correction
layer in two admissible volumes. -/
noncomputable def commonCombinedSmallClusterEquiv
    {d n m k : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (R K L : ℕ)
    (hCn : (O.center (R + 2)).minVolume ≤ n)
    (hCm : (O.center (R + 2)).minVolume ≤ m)
    (hroomN :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    (hroomM :
      O.minVolume + (R + 2) + 1 + R + 1 < m + 1)
    (S : Finset (WindowPlaquette d))
    (hSn : ∀ p ∈ S, p.Fits (n + 1))
    (hSm : ∀ p ∈ S, p.Fits (m + 1))
    (hnearN : localNear
      ((O.center (R + 2)).realizedSupport n hCn)
      (WindowPlaquette.realizedFinset S hSn)
        =
      WindowPlaquette.realizedFinset S hSn)
    (hcardS : S.card ≤ K)
    (hres : (2 * L + 1) + K ≤ R) :
    CommonCombinedSmallClusterTuple
        μ pe β O R L hCn S hSn k
      ≃
    CommonCombinedSmallClusterTuple
        μ pe β O R L hCm S hSm k := by
  let hnearM :=
    (localNear_commonMarkedWindow_iff
      (O.center (R + 2)) hCn hCm S hSn hSm).mp hnearN
  exact
    { toFun := transportCommonCombinedSmallCluster
        μ pe β O R K L hCn hCm hroomN hroomM
          S hSn hSm hnearN hcardS hres
      invFun := transportCommonCombinedSmallCluster
        μ pe β O R K L hCm hCn hroomM hroomN
          S hSm hSn hnearM hcardS hres
      left_inv :=
        transportCommonCombinedSmallCluster_leftInverse
          μ pe β O R K L hCn hCm hroomN hroomM
            S hSn hSm hnearN hcardS hres
      right_inv :=
        transportCommonCombinedSmallCluster_leftInverse
          μ pe β O R K L hCm hCn hroomM hroomN
            S hSm hSn hnearM hcardS hres }

/-- Finite below-cutoff correction layer for one common marked window. -/
noncomputable def commonCombinedSmallClusterLayer
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (R L : ℕ)
    (hC : (O.center (R + 2)).minVolume ≤ n)
    (S : Finset (WindowPlaquette d))
    (hS : ∀ p ∈ S, p.Fits (n + 1))
    (k : ℕ) : ℂ :=
  (((k : ℕ).factorial : ℂ))⁻¹ *
    ∑ X : CommonCombinedSmallClusterTuple
        μ pe β O R L hC S hS k,
      weightedClusterMonomial μ
        (wilsonPlaquetteWeight pe β) X.1

/-- Exact volume independence of a finite common combined-support layer. -/
theorem commonCombinedSmallClusterLayer_eq
    {d n m k : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (R K L : ℕ)
    (hCn : (O.center (R + 2)).minVolume ≤ n)
    (hCm : (O.center (R + 2)).minVolume ≤ m)
    (hroomN :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    (hroomM :
      O.minVolume + (R + 2) + 1 + R + 1 < m + 1)
    (S : Finset (WindowPlaquette d))
    (hSn : ∀ p ∈ S, p.Fits (n + 1))
    (hSm : ∀ p ∈ S, p.Fits (m + 1))
    (hnearN : localNear
      ((O.center (R + 2)).realizedSupport n hCn)
      (WindowPlaquette.realizedFinset S hSn)
        =
      WindowPlaquette.realizedFinset S hSn)
    (hcardS : S.card ≤ K)
    (hres : (2 * L + 1) + K ≤ R) :
    commonCombinedSmallClusterLayer
        μ pe β O R L hCn S hSn k
      =
    commonCombinedSmallClusterLayer
        μ pe β O R L hCm S hSm k := by
  unfold commonCombinedSmallClusterLayer
  congr 1
  let e := commonCombinedSmallClusterEquiv
    (k := k) μ pe β O R K L hCn hCm hroomN hroomM
      S hSn hSm hnearN hcardS hres
  refine Fintype.sum_equiv e _ _ ?_
  intro X
  exact
    weightedClusterMonomial_transportCommonCombinedSmallCluster
      μ pe β O R K L hCn hCm hroomN hroomM
        S hSn hSm hnearN hcardS hres X

/-- The raw below-cutoff correction layer for the combined finite support
is exactly the common-window connected-tuple layer. -/
theorem localCorrectionSmallSeriesTerm_eq_commonCombinedLayer
    {d n q : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (R L : ℕ)
    (hC : (O.center (R + 2)).minVolume ≤ n)
    (S : Finset (WindowPlaquette d))
    (hS : ∀ p ∈ S, p.Fits (n + 1)) :
    localCorrectionSmallSeriesTerm μ pe β
        (((O.center (R + 2)).realizedSupport n hC) ∪
          (WindowPlaquette.realizedFinset S hS).biUnion
            plaquetteSupport)
        L q
      =
    commonCombinedSmallClusterLayer
      μ pe β O R L hC S hS (q + 1) := by
  classical
  let P := connectedLatticePolymerSystem
    (d := d) (N := n + 1) μ pe β
  let SF :=
    ((O.center (R + 2)).realizedSupport n hC) ∪
      (WindowPlaquette.realizedFinset S hS).biUnion
        plaquetteSupport
  let meetSmall : (Fin (q + 1) → P.Polymer) → Prop :=
    fun X =>
      (∃ i, ¬ Disjoint (X i).1 (supportPlaquettes SF)) ∧
      (∑ i, (X i).1.card) < L
  let cluster : (Fin (q + 1) → P.Polymer) → Prop :=
    fun X => KP.IsCluster P X
  let f : (Fin (q + 1) → P.Polymer) → ℂ :=
    fun X => weightedClusterMonomial μ
      (wilsonPlaquetteWeight pe β) X
  have hsubset :
      (Finset.univ.filter fun X => cluster X ∧ meetSmall X) ⊆
        (Finset.univ.filter meetSmall) := by
    intro X hX
    simp only [Finset.mem_filter, Finset.mem_univ,
      true_and] at hX ⊢
    exact hX.2
  have hzero :
      ∀ X ∈ Finset.univ.filter meetSmall,
        X ∉ Finset.univ.filter
          (fun X => cluster X ∧ meetSmall X) →
          f X = 0 := by
    intro X hX hXC
    simp only [Finset.mem_filter, Finset.mem_univ,
      true_and] at hX hXC
    have hncluster : ¬ cluster X := by
      intro hcluster
      exact hXC ⟨hcluster, hX⟩
    have hncluster' : ¬ KP.IsCluster P X := by
      simpa [cluster] using hncluster
    unfold f weightedClusterMonomial
    have hursell :
        KP.ursell
          (weightedLatticePolymerSystem μ
            (wilsonPlaquetteWeight pe β)) X = 0 := by
      apply KP.ursell_eq_zero_of_not_isCluster
      simpa [P, connectedLatticePolymerSystem,
        weightedLatticePolymerSystem] using hncluster'
    rw [hursell]
    simp
  have hraw :
      (∑ X ∈ Finset.univ.filter meetSmall, f X)
        =
      ∑ X ∈ Finset.univ.filter
        (fun X => cluster X ∧ meetSmall X), f X :=
    (Finset.sum_subset hsubset hzero).symm
  have hsubtype :
      (∑ X : CommonCombinedSmallClusterTuple
          μ pe β O R L hC S hS (q + 1), f X.1)
        =
      ∑ X ∈ Finset.univ.filter
        (fun X => cluster X ∧ meetSmall X), f X := by
    simpa [CommonCombinedSmallClusterTuple,
      CombinedSmallClusterTuple, cluster, meetSmall, SF, P] using
      (Finset.sum_subtype_eq_sum_filter
        (p := fun X : Fin (q + 1) → P.Polymer =>
          cluster X ∧ meetSmall X)
        (s := Finset.univ) f)
  unfold localCorrectionSmallSeriesTerm
    commonCombinedSmallClusterLayer
  change (((q + 1).factorial : ℂ))⁻¹ *
      (∑ X ∈ Finset.univ.filter meetSmall, f X)
    =
    (((q + 1).factorial : ℂ))⁻¹ *
      ∑ X : CommonCombinedSmallClusterTuple
        μ pe β O R L hC S hS (q + 1), f X.1
  rw [hraw, ← hsubtype]

/-- The complete below-cutoff correction series pinned to one common
marked window is exactly independent of the admissible finite volume. -/
theorem localCorrectionSmallSeries_commonCombined_eq
    {d n m : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (R K L : ℕ)
    (hCn : (O.center (R + 2)).minVolume ≤ n)
    (hCm : (O.center (R + 2)).minVolume ≤ m)
    (hroomN :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    (hroomM :
      O.minVolume + (R + 2) + 1 + R + 1 < m + 1)
    (S : Finset (WindowPlaquette d))
    (hSn : ∀ p ∈ S, p.Fits (n + 1))
    (hSm : ∀ p ∈ S, p.Fits (m + 1))
    (hnearN : localNear
      ((O.center (R + 2)).realizedSupport n hCn)
      (WindowPlaquette.realizedFinset S hSn)
        =
      WindowPlaquette.realizedFinset S hSn)
    (hcardS : S.card ≤ K)
    (hres : (2 * L + 1) + K ≤ R) :
    (∑' q, localCorrectionSmallSeriesTerm μ pe β
        (((O.center (R + 2)).realizedSupport n hCn) ∪
          (WindowPlaquette.realizedFinset S hSn).biUnion
            plaquetteSupport)
        L q)
      =
    ∑' q, localCorrectionSmallSeriesTerm μ pe β
        (((O.center (R + 2)).realizedSupport m hCm) ∪
          (WindowPlaquette.realizedFinset S hSm).biUnion
            plaquetteSupport)
        L q := by
  apply tsum_congr
  intro q
  rw [localCorrectionSmallSeriesTerm_eq_commonCombinedLayer
      μ pe β O R L hCn S hSn,
    localCorrectionSmallSeriesTerm_eq_commonCombinedLayer
      μ pe β O R L hCm S hSm]
  exact commonCombinedSmallClusterLayer_eq
    μ pe β O R K L hCn hCm hroomN hroomM
      S hSn hSm hnearN hcardS hres

end WindowPolymer

end YangMills
