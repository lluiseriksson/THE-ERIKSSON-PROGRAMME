/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.L1_GibbsMeasure.LocalCenteredWindow

/-!
# Exact transport of centered clusters below a cardinality cutoff

This module packages the finite index set which survives after the
volume-uniform rooted tail has removed all clusters of total plaquette
cardinality at least `L`.  Every remaining cluster has a unique
common-window representative, so these finite index sets are explicitly
equivalent in any two sufficiently large volumes.
-/

namespace YangMills

open MeasureTheory GaugeConfig

namespace WindowPolymer

open Classical

/-- Explicit volume conditions under which the centered radius-`2L` window
fits.  The first field is the honest guard required by finite translation;
the second is the sharper coordinate room used by the geometric decoder. -/
structure CenteredWindowAdmissible
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (L n : ℕ) : Prop where
  center_le : (O.center (2 * L + 2)).minVolume ≤ n
  room :
    O.minVolume + (2 * L + 2) + 1 + (2 * L) + 1 < n + 1

/-- The finite set of connected order-`k` tuples which meet the centered
observable support and have total plaquette cardinality below `L`. -/
def CenteredSmallClusterTuple
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G) (L n : ℕ)
    (hn : CenteredWindowAdmissible O L n) (k : ℕ) :=
  {X : Fin k →
      (connectedLatticePolymerSystem
        (d := d) (N := n + 1) μ pe β).Polymer //
    KP.IsCluster
        (connectedLatticePolymerSystem
          (d := d) (N := n + 1) μ pe β) X ∧
      (∃ i, ¬ Disjoint (X i).1
        (supportPlaquettes
          ((O.center (2 * L + 2)).realizedSupport n hn.center_le))) ∧
      (∑ i, (X i).1.card) < L}

noncomputable instance centeredSmallClusterTupleFintype
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G) (L n : ℕ)
    (hn : CenteredWindowAdmissible O L n) (k : ℕ) :
    Fintype (CenteredSmallClusterTuple μ pe β O L n hn k) := by
  classical
  unfold CenteredSmallClusterTuple
  infer_instance

/-- Data witnessing that a finite-volume tuple is the source realization
of one common-window tuple which also fits in a target volume. -/
structure CommonWindowTuple
    {d n m k : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (X : Fin k →
      (connectedLatticePolymerSystem
        (d := d) (N := n + 1) μ pe β).Polymer) where
  tuple : Fin k → WindowPolymer d
  sourceFits : ∀ j, (tuple j).Fits (n + 1)
  targetFits : ∀ j, (tuple j).Fits (m + 1)
  source_eq : ∀ j,
    (tuple j).toWeightedPolymer μ
      (wilsonPlaquetteWeight pe β) (sourceFits j) = X j

/-- Canonical (by classical choice, unique after realization)
common-window representative of a centered below-cutoff cluster. -/
noncomputable def centeredSmallClusterCommonWindow
    {d n m k : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G) (L : ℕ)
    (hn : CenteredWindowAdmissible O L n)
    (hm : CenteredWindowAdmissible O L m)
    (X : CenteredSmallClusterTuple μ pe β O L n hn k) :
    CommonWindowTuple (m := m) μ pe β X.1 := by
  classical
  let hex :=
    exists_commonWindow_of_centered_smallCluster
      μ pe β O L hn.center_le hn.room hm.room
        X.2.1 X.2.2.1 X.2.2.2
  let Y := Classical.choose hex
  let hrest := Classical.choose_spec hex
  let hYn := Classical.choose hrest
  let hrest' := Classical.choose_spec hrest
  let hYm := Classical.choose hrest'
  let hsource := Classical.choose_spec hrest'
  exact ⟨Y, hYn, hYm, hsource⟩

/-- The target realization of the canonical common-window representative. -/
noncomputable def centeredSmallClusterTargetTuple
    {d n m k : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G) (L : ℕ)
    (hn : CenteredWindowAdmissible O L n)
    (hm : CenteredWindowAdmissible O L m)
    (X : CenteredSmallClusterTuple μ pe β O L n hn k) :
    Fin k →
      (connectedLatticePolymerSystem
        (d := d) (N := m + 1) μ pe β).Polymer :=
  let R := YangMills.WindowPolymer.centeredSmallClusterCommonWindow
    μ pe β O L hn hm X
  fun j => (R.tuple j).toWeightedPolymer μ
    (wilsonPlaquetteWeight pe β) (R.targetFits j)

/-- Target realization preserves the total plaquette cardinality. -/
theorem sum_card_centeredSmallClusterTargetTuple
    {d n m k : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G) (L : ℕ)
    (hn : CenteredWindowAdmissible O L n)
    (hm : CenteredWindowAdmissible O L m)
    (X : CenteredSmallClusterTuple μ pe β O L n hn k) :
    (∑ i, (centeredSmallClusterTargetTuple
      μ pe β O L hn hm X i).1.card)
      = ∑ i, (X.1 i).1.card := by
  let R := YangMills.WindowPolymer.centeredSmallClusterCommonWindow
    μ pe β O L hn hm X
  calc
    (∑ i, (centeredSmallClusterTargetTuple
        μ pe β O L hn hm X i).1.card)
        = ∑ i, (R.tuple i).support.card := by
          apply Finset.sum_congr rfl
          intro i _
          exact card_toWeightedPolymer μ
            (wilsonPlaquetteWeight pe β) (R.tuple i) (R.targetFits i)
    _ = ∑ i, (X.1 i).1.card := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← R.source_eq i]
          exact (card_toWeightedPolymer μ
            (wilsonPlaquetteWeight pe β) (R.tuple i)
              (R.sourceFits i)).symm

/-- Target realization remains a connected cluster. -/
theorem isCluster_centeredSmallClusterTargetTuple
    {d n m k : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G) (L : ℕ)
    (hn : CenteredWindowAdmissible O L n)
    (hm : CenteredWindowAdmissible O L m)
    (X : CenteredSmallClusterTuple μ pe β O L n hn k) :
    KP.IsCluster
      (connectedLatticePolymerSystem
        (d := d) (N := m + 1) μ pe β)
      (centeredSmallClusterTargetTuple μ pe β O L hn hm X) := by
  let R := YangMills.WindowPolymer.centeredSmallClusterCommonWindow
    μ pe β O L hn hm X
  have hiff := isCluster_toWeightedPolymer_iff μ
    (wilsonPlaquetteWeight pe β)
    (wilsonPlaquetteWeight pe β)
    R.tuple R.sourceFits R.targetFits
  apply hiff.mp
  have htuple :
      (fun j => (R.tuple j).toWeightedPolymer μ
        (wilsonPlaquetteWeight pe β) (R.sourceFits j)) = X.1 :=
    funext R.source_eq
  rw [htuple]
  exact X.2.1

/-- Incidence with the centered observable support is transported exactly. -/
theorem meets_centeredSmallClusterTargetTuple
    {d n m k : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G) (L : ℕ)
    (hn : CenteredWindowAdmissible O L n)
    (hm : CenteredWindowAdmissible O L m)
    (X : CenteredSmallClusterTuple μ pe β O L n hn k) :
    ∃ i, ¬ Disjoint
      (centeredSmallClusterTargetTuple μ pe β O L hn hm X i).1
      (supportPlaquettes
        ((O.center (2 * L + 2)).realizedSupport m hm.center_le)) := by
  let C := O.center (2 * L + 2)
  let R := YangMills.WindowPolymer.centeredSmallClusterCommonWindow
    μ pe β O L hn hm X
  obtain ⟨i, hi⟩ := X.2.2.1
  obtain ⟨p, hpXi, hpS⟩ := Finset.not_disjoint_iff.mp hi
  have hpRi : p ∈
      ((R.tuple i).toWeightedPolymer μ
        (wilsonPlaquetteWeight pe β) (R.sourceFits i)).1 := by
    rw [R.source_eq i]
    exact hpXi
  rw [toWeightedPolymer_val] at hpRi
  obtain ⟨q, hqp⟩ :=
    WindowPlaquette.mem_realizedFinset_iff.mp hpRi
  have hqSource :
      q.1.toConcrete (R.sourceFits i q.1 q.2) ∈
        supportPlaquettes
          (WindowPosEdge.realizedFinset C.windowSupport
            (C.windowSupport_fits n hn.center_le)) := by
    rw [C.realizedFinset_windowSupport n hn.center_le]
    simpa [hqp] using hpS
  have hqTarget :=
    (WindowPlaquette.mem_supportPlaquettes_realizedFinset_iff
      C.windowSupport
      (C.windowSupport_fits n hn.center_le)
      (C.windowSupport_fits m hm.center_le)
      q.1 (R.sourceFits i q.1 q.2)
      (R.targetFits i q.1 q.2)).mp hqSource
  refine ⟨i, Finset.not_disjoint_iff.mpr ?_⟩
  refine ⟨q.1.toConcrete (R.targetFits i q.1 q.2), ?_, ?_⟩
  · change q.1.toConcrete (R.targetFits i q.1 q.2) ∈
      ((R.tuple i).toWeightedPolymer μ
        (wilsonPlaquetteWeight pe β) (R.targetFits i)).1
    rw [toWeightedPolymer_val]
    apply WindowPlaquette.mem_realizedFinset_iff.mpr
    exact ⟨q, rfl⟩
  · rw [← C.realizedFinset_windowSupport m hm.center_le]
    exact hqTarget

/-- Transport as an element of the target finite centered-cluster set. -/
noncomputable def transportCenteredSmallCluster
    {d n m k : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G) (L : ℕ)
    (hn : CenteredWindowAdmissible O L n)
    (hm : CenteredWindowAdmissible O L m) :
    CenteredSmallClusterTuple μ pe β O L n hn k →
      CenteredSmallClusterTuple μ pe β O L m hm k :=
  fun X => ⟨centeredSmallClusterTargetTuple μ pe β O L hn hm X,
    isCluster_centeredSmallClusterTargetTuple μ pe β O L hn hm X,
    meets_centeredSmallClusterTargetTuple μ pe β O L hn hm X,
    by
      rw [sum_card_centeredSmallClusterTargetTuple
        μ pe β O L hn hm X]
      exact X.2.2.2⟩

/-- The complete Ursell/activity monomial is unchanged by centered
below-cutoff transport. -/
theorem weightedClusterMonomial_transportCenteredSmallCluster
    {d n m k : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G) (L : ℕ)
    (hn : CenteredWindowAdmissible O L n)
    (hm : CenteredWindowAdmissible O L m)
    (X : CenteredSmallClusterTuple μ pe β O L n hn k) :
    weightedClusterMonomial μ (wilsonPlaquetteWeight pe β) X.1 =
      weightedClusterMonomial μ (wilsonPlaquetteWeight pe β)
        (transportCenteredSmallCluster μ pe β O L hn hm X).1 := by
  let R := YangMills.WindowPolymer.centeredSmallClusterCommonWindow
    μ pe β O L hn hm X
  exact weightedClusterMonomial_eq_of_commonWindow
    μ pe β X.1 R.tuple R.sourceFits R.targetFits R.source_eq

/-- Transport to a second volume and back recovers the original tuple
literally. -/
theorem transportCenteredSmallCluster_leftInverse
    {d n m k : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G) (L : ℕ)
    (hn : CenteredWindowAdmissible O L n)
    (hm : CenteredWindowAdmissible O L m)
    (X : CenteredSmallClusterTuple μ pe β O L n hn k) :
    transportCenteredSmallCluster μ pe β O L hm hn
        (transportCenteredSmallCluster μ pe β O L hn hm X) = X := by
  apply Subtype.ext
  funext j
  let R := YangMills.WindowPolymer.centeredSmallClusterCommonWindow
    μ pe β O L hn hm X
  let X' := transportCenteredSmallCluster μ pe β O L hn hm X
  let S := YangMills.WindowPolymer.centeredSmallClusterCommonWindow
    μ pe β O L hm hn X'
  have hreal :
      (S.tuple j).toWeightedPolymer μ
          (wilsonPlaquetteWeight pe β) (S.sourceFits j)
        =
      (R.tuple j).toWeightedPolymer μ
          (wilsonPlaquetteWeight pe β) (R.targetFits j) := by
    have htarget :
        X'.1 j =
          (R.tuple j).toWeightedPolymer μ
            (wilsonPlaquetteWeight pe β) (R.targetFits j) := by
      change centeredSmallClusterTargetTuple
        μ pe β O L hn hm X j =
          (R.tuple j).toWeightedPolymer μ
            (wilsonPlaquetteWeight pe β) (R.targetFits j)
      rfl
    exact (S.source_eq j).trans htarget
  have hSR : S.tuple j = R.tuple j :=
    toWeightedPolymer_injective_of_fits μ
      (wilsonPlaquetteWeight pe β)
      (S.sourceFits j) (R.targetFits j) hreal
  change
    (S.tuple j).toWeightedPolymer μ
        (wilsonPlaquetteWeight pe β) (S.targetFits j) = X.1 j
  exact (toWeightedPolymer_congr μ
    (wilsonPlaquetteWeight pe β)
    (S.targetFits j) (R.sourceFits j) hSR).trans (R.source_eq j)

/-- Explicit equivalence of the finite centered below-cutoff cluster index
sets in two admissible volumes. -/
noncomputable def centeredSmallClusterEquiv
    {d n m k : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G) (L : ℕ)
    (hn : CenteredWindowAdmissible O L n)
    (hm : CenteredWindowAdmissible O L m) :
    CenteredSmallClusterTuple μ pe β O L n hn k ≃
      CenteredSmallClusterTuple μ pe β O L m hm k where
  toFun := transportCenteredSmallCluster μ pe β O L hn hm
  invFun := transportCenteredSmallCluster μ pe β O L hm hn
  left_inv := transportCenteredSmallCluster_leftInverse
    μ pe β O L hn hm
  right_inv := transportCenteredSmallCluster_leftInverse
    μ pe β O L hm hn

/-- The finite below-cutoff connected-cluster layer, indexed only by tuples
whose Ursell coefficient can contribute. -/
noncomputable def centeredSmallClusterLayer
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G) (L : ℕ)
    (hn : CenteredWindowAdmissible O L n) (k : ℕ) : ℂ :=
  (((k : ℕ).factorial : ℂ))⁻¹ *
    ∑ X : CenteredSmallClusterTuple μ pe β O L n hn k,
      weightedClusterMonomial μ (wilsonPlaquetteWeight pe β) X.1

/-- Exact equality of the finite connected-cluster layer in any two
admissible volumes. -/
theorem centeredSmallClusterLayer_eq
    {d n m k : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G) (L : ℕ)
    (hn : CenteredWindowAdmissible O L n)
    (hm : CenteredWindowAdmissible O L m) :
    centeredSmallClusterLayer μ pe β O L hn k =
      centeredSmallClusterLayer μ pe β O L hm k := by
  unfold centeredSmallClusterLayer
  congr 1
  let e := centeredSmallClusterEquiv (k := k) μ pe β O L hn hm
  refine Fintype.sum_equiv e _ _ ?_
  intro X
  exact weightedClusterMonomial_transportCenteredSmallCluster
    μ pe β O L hn hm X

end WindowPolymer

end YangMills
