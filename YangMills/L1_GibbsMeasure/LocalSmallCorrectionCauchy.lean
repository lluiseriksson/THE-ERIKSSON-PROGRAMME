/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.L1_GibbsMeasure.LocalSmallClusterTransport

/-!
# Exact Cauchy transport for the below-cutoff local correction

Disconnected tuples in the raw finite sum have zero Ursell coefficient.
After removing them, the sum is exactly the finite centered-cluster layer
from `LocalSmallClusterTransport`, hence it is independent of the admissible
finite volume.
-/

namespace YangMills

open MeasureTheory GaugeConfig

namespace WindowPolymer

open Classical

/-- The raw below-cutoff finite tuple sum equals the subtype sum over
connected tuples; all discarded tuples have zero Ursell coefficient. -/
theorem localCorrectionSmallSeriesTerm_eq_centeredSmallClusterLayer
    {d n q : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G) (L : ℕ)
    (hn : CenteredWindowAdmissible O L n) :
    localCorrectionSmallSeriesTerm μ pe β
        ((O.center (2 * L + 2)).realizedSupport n hn.center_le)
        L q
      =
    centeredSmallClusterLayer μ pe β O L hn (q + 1) := by
  classical
  let P := connectedLatticePolymerSystem
    (d := d) (N := n + 1) μ pe β
  let meetSmall : (Fin (q + 1) → P.Polymer) → Prop :=
    fun X =>
      (∃ i, ¬ Disjoint (X i).1
        (supportPlaquettes
          ((O.center (2 * L + 2)).realizedSupport n hn.center_le))) ∧
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
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hX ⊢
    exact hX.2
  have hzero :
      ∀ X ∈ Finset.univ.filter meetSmall,
        X ∉ Finset.univ.filter (fun X => cluster X ∧ meetSmall X) →
          f X = 0 := by
    intro X hX hXC
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hX hXC
    have hncluster : ¬ cluster X := by
      intro hcluster
      exact hXC ⟨hcluster, hX⟩
    have hncluster' : ¬ KP.IsCluster P X := by
      simpa [cluster] using hncluster
    unfold f weightedClusterMonomial
    have hursell :
        KP.ursell
          (weightedLatticePolymerSystem μ (wilsonPlaquetteWeight pe β)) X
            = 0 := by
      apply KP.ursell_eq_zero_of_not_isCluster
      simpa [P, connectedLatticePolymerSystem,
        weightedLatticePolymerSystem] using hncluster'
    rw [hursell]
    simp
  have hraw :
      (∑ X ∈ Finset.univ.filter meetSmall, f X)
        =
      ∑ X ∈ Finset.univ.filter (fun X => cluster X ∧ meetSmall X), f X := by
    exact (Finset.sum_subset hsubset hzero).symm
  have hsubtype :
      (∑ X : CenteredSmallClusterTuple μ pe β O L n hn (q + 1),
          f X.1)
        =
      ∑ X ∈ Finset.univ.filter (fun X => cluster X ∧ meetSmall X), f X := by
    simpa [CenteredSmallClusterTuple, cluster, meetSmall, P] using
      (Finset.sum_subtype_eq_sum_filter
        (p := fun X : Fin (q + 1) → P.Polymer =>
          cluster X ∧ meetSmall X)
        (s := Finset.univ)
        f)
  unfold localCorrectionSmallSeriesTerm centeredSmallClusterLayer
  change (((q + 1).factorial : ℂ))⁻¹ *
      (∑ X ∈ Finset.univ.filter meetSmall, f X)
    =
    (((q + 1).factorial : ℂ))⁻¹ *
      ∑ X : CenteredSmallClusterTuple μ pe β O L n hn (q + 1), f X.1
  rw [hraw, ← hsubtype]

/-- **Exact volume independence of every below-cutoff correction layer.** -/
theorem localCorrectionSmallSeriesTerm_centered_eq
    {d n m q : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G) (L : ℕ)
    (hn : CenteredWindowAdmissible O L n)
    (hm : CenteredWindowAdmissible O L m) :
    localCorrectionSmallSeriesTerm μ pe β
        ((O.center (2 * L + 2)).realizedSupport n hn.center_le)
        L q
      =
    localCorrectionSmallSeriesTerm μ pe β
        ((O.center (2 * L + 2)).realizedSupport m hm.center_le)
        L q := by
  rw [localCorrectionSmallSeriesTerm_eq_centeredSmallClusterLayer
      μ pe β O L hn,
    localCorrectionSmallSeriesTerm_eq_centeredSmallClusterLayer
      μ pe β O L hm]
  exact centeredSmallClusterLayer_eq μ pe β O L hn hm

/-- The complete below-cutoff correction series is exactly independent of
the admissible finite volume after centering the local observable. -/
theorem localCorrectionSmallSeries_centered_eq
    {d n m : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G) (L : ℕ)
    (hn : CenteredWindowAdmissible O L n)
    (hm : CenteredWindowAdmissible O L m) :
    (∑' q, localCorrectionSmallSeriesTerm μ pe β
        ((O.center (2 * L + 2)).realizedSupport n hn.center_le)
        L q)
      =
    ∑' q, localCorrectionSmallSeriesTerm μ pe β
        ((O.center (2 * L + 2)).realizedSupport m hm.center_le)
        L q :=
  tsum_congr fun q =>
    localCorrectionSmallSeriesTerm_centered_eq
      μ pe β O L hn hm (q := q)

/-- **Quantitative Cauchy estimate for the exact local correction.**

The below-cutoff parts agree exactly by common-window transport.  Each
remaining part is a rooted KP tail, hence two fitting volumes differ by at
most twice the uniform exponential tail. -/
theorem norm_localCorrectionSeries_centered_sub_le_volumeUniform
    {d n m : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (t ε : ℝ) (ht0 : 0 ≤ t) (hε0 : 0 ≤ ε)
    (hr₀ : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      ((Real.exp (|β| * B) - 1) * Real.exp (t + ε)) < 1)
    (hsmall₀ : ((16 * d : ℕ) : ℝ) *
      (((Real.exp (|β| * B) - 1) * Real.exp (t + ε)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          ((Real.exp (|β| * B) - 1) * Real.exp (t + ε)))) ≤ t)
    (hr₁ : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      ((Real.exp (|β| * B) - 1) * Real.exp (t + ε + 1)) < 1)
    (hsmall₁ : ((16 * d : ℕ) : ℝ) *
      (((Real.exp (|β| * B) - 1) * Real.exp (t + ε + 1)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          ((Real.exp (|β| * B) - 1) * Real.exp (t + ε + 1)))) ≤ t)
    (O : CompatibleLocalObservable d G) (L : ℕ)
    (hn : CenteredWindowAdmissible O L n)
    (hm : CenteredWindowAdmissible O L m) :
    ‖(∑' q, localCorrectionSeriesTerm μ pe β
          ((O.center (2 * L + 2)).realizedSupport n hn.center_le)
          0 q)
        -
      ∑' q, localCorrectionSeriesTerm μ pe β
          ((O.center (2 * L + 2)).realizedSupport m hm.center_le)
          0 q‖
      ≤
    2 * (Real.exp (-(ε * L)) *
      ((2 * t) *
        ((Fintype.card O.Support : ℝ) * (4 * (d : ℝ))))) := by
  let SFn :=
    (O.center (2 * L + 2)).realizedSupport n hn.center_le
  let SFm :=
    (O.center (2 * L + 2)).realizedSupport m hm.center_le
  let fulln := ∑' q, localCorrectionSeriesTerm μ pe β SFn 0 q
  let fullm := ∑' q, localCorrectionSeriesTerm μ pe β SFm 0 q
  let smalln := ∑' q, localCorrectionSmallSeriesTerm μ pe β SFn L q
  let smallm := ∑' q, localCorrectionSmallSeriesTerm μ pe β SFm L q
  let C := Real.exp (-(ε * L)) *
    ((2 * t) * ((Fintype.card O.Support : ℝ) * (4 * (d : ℝ))))
  have hsmall : smalln = smallm := by
    exact localCorrectionSmallSeries_centered_eq
      μ pe β O L hn hm
  have hcardn : SFn.card = Fintype.card O.Support := by
    change (((O.center (2 * L + 2)).realizedSupport
      n hn.center_le).card = Fintype.card O.Support)
    rw [CompatibleLocalObservable.card_realizedSupport]
    exact CompatibleLocalObservable.card_support_center O _
  have hcardm : SFm.card = Fintype.card O.Support := by
    change (((O.center (2 * L + 2)).realizedSupport
      m hm.center_le).card = Fintype.card O.Support)
    rw [CompatibleLocalObservable.card_realizedSupport]
    exact CompatibleLocalObservable.card_support_center O _
  have hnTail : ‖fulln - smalln‖ ≤ C := by
    have h := norm_localCorrectionSeries_sub_small_le_volumeUniform
      μ hpe β t ε ht0 hε0 hr₀ hsmall₀ hr₁ hsmall₁ SFn L
    change ‖(∑' q, localCorrectionSeriesTerm μ pe β SFn 0 q)
        - ∑' q, localCorrectionSmallSeriesTerm μ pe β SFn L q‖ ≤ C
    calc
      _ ≤ Real.exp (-(ε * L)) *
          ((2 * t) * ((SFn.card : ℝ) * (4 * (d : ℝ)))) := h
      _ = C := by rw [hcardn]
  have hmTail : ‖fullm - smallm‖ ≤ C := by
    have h := norm_localCorrectionSeries_sub_small_le_volumeUniform
      μ hpe β t ε ht0 hε0 hr₀ hsmall₀ hr₁ hsmall₁ SFm L
    change ‖(∑' q, localCorrectionSeriesTerm μ pe β SFm 0 q)
        - ∑' q, localCorrectionSmallSeriesTerm μ pe β SFm L q‖ ≤ C
    calc
      _ ≤ Real.exp (-(ε * L)) *
          ((2 * t) * ((SFm.card : ℝ) * (4 * (d : ℝ)))) := h
      _ = C := by rw [hcardm]
  change ‖fulln - fullm‖ ≤ 2 * C
  calc
    ‖fulln - fullm‖
        = ‖(fulln - smalln) - (fullm - smallm)‖ := by
          rw [hsmall]
          congr 1
          ring
    _ ≤ ‖fulln - smalln‖ + ‖fullm - smallm‖ := norm_sub_le _ _
    _ ≤ C + C := add_le_add hnTail hmTail
    _ = 2 * C := by ring

end WindowPolymer

end YangMills
