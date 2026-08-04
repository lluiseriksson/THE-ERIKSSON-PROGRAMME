/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.L1_GibbsMeasure.LocalCorrectionTail

/-!
# Exact local correction series and its volume-uniform tail

`KP.clusterSum_sub_restrict` produces a complex series over tuples with at
least one polymer outside the restricted far gas.  This module identifies
that predicate exactly with meeting the plaquette support discarded by
`localFarRegion`, and records the norm-majorized size tail as a summable
complex series.
-/

namespace YangMills

open MeasureTheory GaugeConfig

namespace WindowPolymer

open Classical

/-- The complex order-`n+1` local correction term restricted to tuples of
total plaquette cardinality at least `L`. -/
noncomputable def localCorrectionSeriesTerm
    {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (SF : Finset (PosEdge d N)) (L n : ℕ) : ℂ :=
  let P := connectedLatticePolymerSystem
    (d := d) (N := N) μ pe β
  (((n + 1).factorial : ℂ))⁻¹ *
    ∑ X ∈ (Finset.univ :
        Finset (Fin (n + 1) → P.Polymer)).filter
      (fun X =>
        (∃ i, ¬ Disjoint (X i).1 (supportPlaquettes SF)) ∧
          L ≤ ∑ i, (X i).1.card),
      (KP.ursell P X : ℂ) * ∏ i, P.activity (X i)

/-- The complementary below-cutoff part of the local correction layer. -/
noncomputable def localCorrectionSmallSeriesTerm
    {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (SF : Finset (PosEdge d N)) (L n : ℕ) : ℂ :=
  let P := connectedLatticePolymerSystem
    (d := d) (N := N) μ pe β
  (((n + 1).factorial : ℂ))⁻¹ *
    ∑ X ∈ (Finset.univ :
        Finset (Fin (n + 1) → P.Polymer)).filter
      (fun X =>
        (∃ i, ¬ Disjoint (X i).1 (supportPlaquettes SF)) ∧
          (∑ i, (X i).1.card) < L),
      (KP.ursell P X : ℂ) * ∏ i, P.activity (X i)

/-- Exact layer partition into below-cutoff and tail terms. -/
theorem localCorrectionSeriesTerm_zero_eq_small_add_tail
    {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (SF : Finset (PosEdge d N)) (L n : ℕ) :
    localCorrectionSeriesTerm μ pe β SF 0 n
      =
      localCorrectionSmallSeriesTerm μ pe β SF L n
        + localCorrectionSeriesTerm μ pe β SF L n := by
  classical
  let P := connectedLatticePolymerSystem
    (d := d) (N := N) μ pe β
  let meet : (Fin (n + 1) → P.Polymer) → Prop :=
    fun X => ∃ i, ¬ Disjoint (X i).1 (supportPlaquettes SF)
  let small : (Fin (n + 1) → P.Polymer) → Prop :=
    fun X => (∑ i, (X i).1.card) < L
  let f : (Fin (n + 1) → P.Polymer) → ℂ :=
    fun X => (KP.ursell P X : ℂ) * ∏ i, P.activity (X i)
  have hpart := Finset.sum_filter_add_sum_filter_not
    ((Finset.univ :
      Finset (Fin (n + 1) → P.Polymer)).filter meet) small f
  unfold localCorrectionSeriesTerm localCorrectionSmallSeriesTerm
  change (((n + 1).factorial : ℂ))⁻¹ *
      ∑ X ∈ (Finset.univ :
        Finset (Fin (n + 1) → P.Polymer)).filter
        (fun X => meet X ∧ 0 ≤ ∑ i, (X i).1.card), f X
    =
    (((n + 1).factorial : ℂ))⁻¹ *
        ∑ X ∈ (Finset.univ :
          Finset (Fin (n + 1) → P.Polymer)).filter
          (fun X => meet X ∧ small X), f X
      +
      (((n + 1).factorial : ℂ))⁻¹ *
        ∑ X ∈ (Finset.univ :
          Finset (Fin (n + 1) → P.Polymer)).filter
          (fun X => meet X ∧ L ≤ ∑ i, (X i).1.card), f X
  rw [← mul_add]
  congr 1
  have hpart' :
      (∑ X ∈ (Finset.univ :
          Finset (Fin (n + 1) → P.Polymer)).filter
          (fun X => meet X ∧ small X), f X)
        +
      ∑ X ∈ (Finset.univ :
          Finset (Fin (n + 1) → P.Polymer)).filter
          (fun X => meet X ∧ ¬ small X), f X
        =
      ∑ X ∈ (Finset.univ :
          Finset (Fin (n + 1) → P.Polymer)).filter meet, f X := by
    simpa only [Finset.filter_filter, and_comm, and_left_comm,
      and_assoc] using hpart
  rw [show (∑ X ∈ (Finset.univ :
      Finset (Fin (n + 1) → P.Polymer)).filter
      (fun X => meet X ∧ L ≤ ∑ i, (X i).1.card), f X)
      =
      ∑ X ∈ (Finset.univ :
        Finset (Fin (n + 1) → P.Polymer)).filter
        (fun X => meet X ∧ ¬ small X), f X by
        refine Finset.sum_congr ?_ fun _ _ => rfl
        refine Finset.filter_congr fun X _ => ?_
        simp only [small, Nat.not_lt]]
  rw [hpart']
  refine Finset.sum_congr ?_ fun _ _ => rfl
  refine Finset.filter_congr fun X _ => ?_
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, Nat.zero_le _⟩

/-- The complex local correction layer is bounded by the real rooted-tail
majorant from `LocalCorrectionTail`. -/
theorem norm_localCorrectionSeriesTerm_le
    {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (SF : Finset (PosEdge d N)) (L n : ℕ) :
    ‖localCorrectionSeriesTerm μ pe β SF L n‖
      ≤ localCorrectionTailLayer μ pe β SF L n := by
  classical
  unfold localCorrectionSeriesTerm localCorrectionTailLayer
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun X _ => ?_
  rw [norm_mul, norm_prod]
  refine mul_le_mul_of_nonneg_right ?_
    (Finset.prod_nonneg fun i _ => norm_nonneg _)
  rw [show ((KP.ursell
      (connectedLatticePolymerSystem
        (d := d) (N := N) μ pe β) X : ℤ) : ℂ)
      =
      (((KP.ursell
        (connectedLatticePolymerSystem
          (d := d) (N := N) μ pe β) X : ℤ) : ℝ) : ℂ) from by
        push_cast
        ring]
  rw [Complex.norm_real, Real.norm_eq_abs]

/-- **Summability and norm bound for the complete complex correction tail.** -/
theorem localCorrectionSeries_summable_volumeUniform
    {d N : ℕ} [NeZero d] [NeZero N]
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
    (SF : Finset (PosEdge d N)) (L : ℕ) :
    Summable (fun n => localCorrectionSeriesTerm μ pe β SF L n) ∧
      ‖∑' n, localCorrectionSeriesTerm μ pe β SF L n‖
        ≤ Real.exp (-(ε * L)) *
          ((2 * t) * ((SF.card : ℝ) * (4 * (d : ℝ)))) := by
  classical
  have hreal := localCorrectionTail_summable_volumeUniform
    μ hpe β t ε ht0 hε0 hr₀ hsmall₀ hr₁ hsmall₁ SF L
  have hnorm : Summable
      (fun n => ‖localCorrectionSeriesTerm μ pe β SF L n‖) :=
    Summable.of_nonneg_of_le
      (fun n => norm_nonneg _)
      (fun n => norm_localCorrectionSeriesTerm_le μ pe β SF L n)
      hreal.1
  have hcomplex :
      Summable (fun n => localCorrectionSeriesTerm μ pe β SF L n) :=
    Summable.of_norm hnorm
  refine ⟨hcomplex, ?_⟩
  calc
    ‖∑' n, localCorrectionSeriesTerm μ pe β SF L n‖
        ≤ ∑' n, ‖localCorrectionSeriesTerm μ pe β SF L n‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n, localCorrectionTailLayer μ pe β SF L n :=
      hnorm.tsum_le_tsum
        (fun n => norm_localCorrectionSeriesTerm_le μ pe β SF L n)
        hreal.1
    _ ≤ Real.exp (-(ε * L)) *
        ((2 * t) * ((SF.card : ℝ) * (4 * (d : ℝ)))) :=
      hreal.2

/-- The below-cutoff series is summable, and the complete local correction
splits exactly into the below-cutoff series plus its exponentially small
tail. -/
theorem localCorrectionSeries_eq_small_add_tail
    {d N : ℕ} [NeZero d] [NeZero N]
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
    (SF : Finset (PosEdge d N)) (L : ℕ) :
    Summable (fun n =>
      localCorrectionSmallSeriesTerm μ pe β SF L n) ∧
    (∑' n, localCorrectionSeriesTerm μ pe β SF 0 n)
      =
      (∑' n, localCorrectionSmallSeriesTerm μ pe β SF L n)
        + ∑' n, localCorrectionSeriesTerm μ pe β SF L n := by
  classical
  have hfull :=
    (localCorrectionSeries_summable_volumeUniform
      μ hpe β t ε ht0 hε0 hr₀ hsmall₀ hr₁ hsmall₁ SF 0).1
  have htail :=
    (localCorrectionSeries_summable_volumeUniform
      μ hpe β t ε ht0 hε0 hr₀ hsmall₀ hr₁ hsmall₁ SF L).1
  have hsmall : Summable (fun n =>
      localCorrectionSmallSeriesTerm μ pe β SF L n) := by
    refine (hfull.sub htail).congr fun n => ?_
    rw [localCorrectionSeriesTerm_zero_eq_small_add_tail
      μ pe β SF L n]
    ring
  refine ⟨hsmall, ?_⟩
  rw [← Summable.tsum_add hsmall htail]
  exact tsum_congr fun n =>
    localCorrectionSeriesTerm_zero_eq_small_add_tail
      μ pe β SF L n

/-- **The full local correction is exponentially close to its exact
below-cutoff part.** -/
theorem norm_localCorrectionSeries_sub_small_le_volumeUniform
    {d N : ℕ} [NeZero d] [NeZero N]
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
    (SF : Finset (PosEdge d N)) (L : ℕ) :
    ‖(∑' n, localCorrectionSeriesTerm μ pe β SF 0 n)
        - ∑' n, localCorrectionSmallSeriesTerm μ pe β SF L n‖
      ≤ Real.exp (-(ε * L)) *
        ((2 * t) * ((SF.card : ℝ) * (4 * (d : ℝ)))) := by
  have hsplit := (localCorrectionSeries_eq_small_add_tail
    μ hpe β t ε ht0 hε0 hr₀ hsmall₀ hr₁ hsmall₁ SF L).2
  have htail := (localCorrectionSeries_summable_volumeUniform
    μ hpe β t ε ht0 hε0 hr₀ hsmall₀ hr₁ hsmall₁ SF L).2
  rw [hsplit]
  simpa using htail

/-- A polymer is outside the local far region exactly when it meets the
finite discarded plaquette support. -/
lemma not_subset_localFarRegion_iff_not_disjoint_supportPlaquettes
    {d N : ℕ} [NeZero d] [NeZero N]
    {SF : Finset (PosEdge d N)}
    {S₀ c : Finset (ConcretePlaquette d N)} :
    ¬ c ⊆ localFarRegion SF S₀
      ↔ ¬ Disjoint c
        (supportPlaquettes (SF ∪ S₀.biUnion plaquetteSupport)) := by
  classical
  rw [← localFarRegion_compl_eq_supportPlaquettes_union SF S₀]
  constructor
  · intro hc
    obtain ⟨p, hpc, hpF⟩ := Finset.not_subset.mp hc
    exact Finset.not_disjoint_iff.mpr
      ⟨p, hpc, Finset.mem_compl.mpr hpF⟩
  · intro hc hsub
    rw [Finset.not_disjoint_iff] at hc
    obtain ⟨p, hpc, hpFc⟩ := hc
    exact (Finset.mem_compl.mp hpFc) (hsub hpc)

/-- **Exact restriction correction as a local series.**

The extensive full and restricted cluster sums are not estimated separately:
their algebraic difference is exactly the `L=0` local series pinned to the
combined observable/marked support. -/
theorem clusterSum_sub_localFarRegion_eq_localCorrectionSeries
    {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (SF : Finset (PosEdge d N))
    (S₀ : Finset (ConcretePlaquette d N))
    {a : (connectedLatticePolymerSystem
      (d := d) (N := N) μ pe β).Polymer → ℝ}
    (hkp : KP.KPCriterion
      (connectedLatticePolymerSystem
        (d := d) (N := N) μ pe β) a) :
    KP.clusterSum
        (connectedLatticePolymerSystem
          (d := d) (N := N) μ pe β)
      -
      KP.clusterSum
        ((connectedLatticePolymerSystem
          (d := d) (N := N) μ pe β).restrict
          (Finset.univ.filter
            (fun c => c.1 ⊆ localFarRegion SF S₀)))
      =
      ∑' n, localCorrectionSeriesTerm μ pe β
        (SF ∪ S₀.biUnion plaquetteSupport) 0 n := by
  classical
  let P := connectedLatticePolymerSystem
    (d := d) (N := N) μ pe β
  let Λ : Finset P.Polymer :=
    Finset.univ.filter (fun c => c.1 ⊆ localFarRegion SF S₀)
  rw [KP.clusterSum_sub_restrict hkp Λ]
  refine tsum_congr fun n => ?_
  unfold localCorrectionSeriesTerm
  change (((n + 1).factorial : ℂ))⁻¹ *
      ∑ X ∈ (Finset.univ :
        Finset (Fin (n + 1) → P.Polymer)).filter
        (fun X => ¬ ∀ i, X i ∈ Λ),
        (KP.ursell P X : ℂ) * ∏ i, P.activity (X i)
    =
    (((n + 1).factorial : ℂ))⁻¹ *
      ∑ X ∈ (Finset.univ :
        Finset (Fin (n + 1) → P.Polymer)).filter
        (fun X =>
          (∃ i, ¬ Disjoint (X i).1
            (supportPlaquettes
              (SF ∪ S₀.biUnion plaquetteSupport))) ∧
          0 ≤ ∑ i, (X i).1.card),
        (KP.ursell P X : ℂ) * ∏ i, P.activity (X i)
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  refine Finset.filter_congr fun X _ => ?_
  simp only [Λ, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    push_neg at h
    obtain ⟨i, hi⟩ := h
    exact ⟨⟨i,
      (not_subset_localFarRegion_iff_not_disjoint_supportPlaquettes).mp
        hi⟩, by omega⟩
  · rintro ⟨⟨i, hi⟩, _⟩ hall
    exact
      ((not_subset_localFarRegion_iff_not_disjoint_supportPlaquettes).mpr
        hi) (hall i)

end WindowPolymer

end YangMills
