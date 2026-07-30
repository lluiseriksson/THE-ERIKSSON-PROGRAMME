/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.L1_GibbsMeasure.LocalFreeBoundary

/-!
# Inclusion-exclusion for a local correction and a free boundary

Both the periodic local correction and the free-boundary correction are
differences of cluster sums inside one ambient polymer system.  Their
difference is not estimated by separating extensive cluster sums.  It is
identified algebraically with the absolutely summable subseries of tuples
which simultaneously leave the local far region and the free box.
-/

namespace YangMills

open MeasureTheory GaugeConfig

namespace KP

open Classical

/-- One cluster-series layer selected by an arbitrary tuple predicate. -/
noncomputable def filteredClusterSeriesTerm
    (P : PolymerSystem) [Fintype P.Polymer]
    (Q : ∀ n, (Fin (n + 1) → P.Polymer) → Prop) (n : ℕ) : ℂ :=
  (((n + 1).factorial : ℂ))⁻¹ *
    ∑ X ∈ (Finset.univ :
        Finset (Fin (n + 1) → P.Polymer)).filter (Q n),
      (ursell P X : ℂ) * ∏ i, P.activity (X i)

/-- Every predicate-filtered cluster series is absolutely summable under KP.
This is only a subseries domination by the banked sharp cluster weight. -/
theorem filteredClusterSeries_summable
    (P : PolymerSystem) [Fintype P.Polymer]
    {a : P.Polymer → ℝ} (hkp : KPCriterion P a)
    (Q : ∀ n, (Fin (n + 1) → P.Polymer) → Prop) :
    Summable (fun n => filteredClusterSeriesTerm P Q n) := by
  have hnorm : ∀ n, ‖filteredClusterSeriesTerm P Q n‖ ≤ clusterWeight P n := by
    intro n
    unfold filteredClusterSeriesTerm clusterWeight
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans
      (Finset.sum_le_sum (fun X _ => ?_))
      (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun _ _ _ => by positivity))
    rw [norm_mul, norm_prod]
    rw [show ((ursell P X : ℤ) : ℂ) =
        (((ursell P X : ℤ) : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs]
  exact Summable.of_norm
    (Summable.of_nonneg_of_le
      (fun n => norm_nonneg _)
      hnorm
      (kp_clusterWeight_summable_sharp P hkp))

/-- The intersection of two polymer restrictions, represented in the
ambient polymer type. -/
noncomputable def restrictionInter
    (P : PolymerSystem) [Fintype P.Polymer]
    (Λ Δ : Finset P.Polymer) :
    Finset P.Polymer :=
  Finset.univ.filter (fun c => c ∈ Λ ∧ c ∈ Δ)

/-- Difference between a restriction to `Δ` and the further restriction to
`Λ ∩ Δ`, written as an ambient tuple series. -/
theorem clusterSum_restrict_sub_inter_eq
    (P : PolymerSystem) [Fintype P.Polymer]
    {a : P.Polymer → ℝ} (hkp : KPCriterion P a)
    (Λ Δ : Finset P.Polymer) :
    clusterSum (P.restrict Δ) -
        clusterSum (P.restrict (restrictionInter P Λ Δ))
      =
    ∑' n, filteredClusterSeriesTerm P
      (fun _ X => ((∀ i, X i ∈ Δ) ∧ ¬ ∀ i, X i ∈ Λ) ∧
        IsCluster P X) n := by
  let I := restrictionInter P Λ Δ
  let allΔ : ∀ n, (Fin (n + 1) → P.Polymer) → Prop :=
    fun _ X => ∀ i, X i ∈ Δ
  let allI : ∀ n, (Fin (n + 1) → P.Polymer) → Prop :=
    fun _ X => ∀ i, X i ∈ I
  have hΔ := filteredClusterSeries_summable P hkp allΔ
  have hI := filteredClusterSeries_summable P hkp allI
  have heqΔ :
      (fun n : ℕ => (((n + 1).factorial : ℂ))⁻¹ *
        ∑ X ∈ (Finset.univ :
            Finset (Fin (n + 1) → P.Polymer)).filter
            (fun X => ∀ i, X i ∈ Δ),
          (ursell P X : ℂ) * ∏ i, P.activity (X i))
        =
      fun n => filteredClusterSeriesTerm P allΔ n := by
    funext n
    unfold filteredClusterSeriesTerm
    congr 2
    ext X
    simp [allΔ]
  have heqI :
      (fun n : ℕ => (((n + 1).factorial : ℂ))⁻¹ *
        ∑ X ∈ (Finset.univ :
            Finset (Fin (n + 1) → P.Polymer)).filter
            (fun X => ∀ i, X i ∈ restrictionInter P Λ Δ),
          (ursell P X : ℂ) * ∏ i, P.activity (X i))
        =
      fun n => filteredClusterSeriesTerm P allI n := by
    funext n
    unfold filteredClusterSeriesTerm
    congr 2
    ext X
    simp [allI, I]
  rw [clusterSum_restrict, clusterSum_restrict]
  rw [congrArg tsum heqΔ, congrArg tsum heqI]
  rw [← hΔ.tsum_sub hI]
  refine tsum_congr fun n => ?_
  unfold filteredClusterSeriesTerm
  rw [← mul_sub]
  congr 1
  dsimp only [allΔ, allI, I]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun X _ => ?_
  by_cases hΔX : ∀ i, X i ∈ Δ
  · by_cases hΛX : ∀ i, X i ∈ Λ
    · simp [hΔX, hΛX, restrictionInter]
    · by_cases hX : IsCluster P X
      · simp [hΔX, hΛX, hX, restrictionInter]
      · rw [ursell_eq_zero_of_not_isCluster P X hX]
        simp [hΔX, hΛX, hX, restrictionInter]
  · have hIX : ¬ ∀ i, X i ∈ restrictionInter P Λ Δ := by
      intro h
      apply hΔX
      intro i
      have hi : X i ∈ Λ ∧ X i ∈ Δ := by
        simpa [restrictionInter] using h i
      exact hi.2
    simp [hΔX, hIX]

/-- **Exact double-restriction inclusion-exclusion.**

The left side is the periodic local correction minus the corresponding
free-boundary correction.  The right side contains precisely tuples which
leave both restrictions.  No extensive cluster sum is bounded separately. -/
theorem clusterSum_doubleRestriction_eq
    (P : PolymerSystem) [Fintype P.Polymer]
    {a : P.Polymer → ℝ} (hkp : KPCriterion P a)
    (Λ Δ : Finset P.Polymer) :
    (clusterSum P - clusterSum (P.restrict Λ)) -
        (clusterSum (P.restrict Δ) -
          clusterSum (P.restrict (restrictionInter P Λ Δ)))
      =
    ∑' n, filteredClusterSeriesTerm P
      (fun _ X => ((¬ ∀ i, X i ∈ Λ) ∧ (¬ ∀ i, X i ∈ Δ)) ∧
        IsCluster P X) n := by
  let outsideΛ : ∀ n, (Fin (n + 1) → P.Polymer) → Prop :=
    fun _ X => ¬ ∀ i, X i ∈ Λ
  let inΔoutsideΛ : ∀ n, (Fin (n + 1) → P.Polymer) → Prop :=
    fun _ X => ((∀ i, X i ∈ Δ) ∧ ¬ ∀ i, X i ∈ Λ) ∧
      IsCluster P X
  have hA := filteredClusterSeries_summable P hkp outsideΛ
  have hD := filteredClusterSeries_summable P hkp inΔoutsideΛ
  have heqA :
      (fun n : ℕ => (((n + 1).factorial : ℂ))⁻¹ *
        ∑ X ∈ (Finset.univ :
            Finset (Fin (n + 1) → P.Polymer)).filter
            (fun X => ¬ ∀ i, X i ∈ Λ),
          (ursell P X : ℂ) * ∏ i, P.activity (X i))
        =
      fun n => filteredClusterSeriesTerm P outsideΛ n := by
    funext n
    unfold filteredClusterSeriesTerm
    congr 2
    ext X
    simp [outsideΛ]
  have heqD :
      (fun n => filteredClusterSeriesTerm P
          (fun _ X => ((∀ i, X i ∈ Δ) ∧ ¬ ∀ i, X i ∈ Λ) ∧
            IsCluster P X) n)
        =
      fun n => filteredClusterSeriesTerm P inΔoutsideΛ n := by
    funext n
    unfold filteredClusterSeriesTerm
    congr 2
  rw [clusterSum_sub_restrict hkp Λ,
    clusterSum_restrict_sub_inter_eq P hkp Λ Δ]
  rw [congrArg tsum heqA, congrArg tsum heqD]
  rw [← hA.tsum_sub hD]
  refine tsum_congr fun n => ?_
  unfold filteredClusterSeriesTerm
  rw [← mul_sub]
  congr 1
  dsimp only [outsideΛ, inΔoutsideΛ]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun X _ => ?_
  by_cases hΛX : ∀ i, X i ∈ Λ
  · simp [hΛX]
  · by_cases hΔX : ∀ i, X i ∈ Δ
    · by_cases hX : IsCluster P X
      · simp [hΛX, hΔX, hX]
      · rw [ursell_eq_zero_of_not_isCluster P X hX]
        simp [hΛX, hΔX, hX]
    · by_cases hX : IsCluster P X
      · simp [hΛX, hΔX, hX]
      · rw [ursell_eq_zero_of_not_isCluster P X hX]
        simp [hΛX, hΔX, hX]

end KP

namespace WindowPolymer

open Classical

/-- Ratio of two genuine region-restricted Mayer products.  Both partition
functions are converted to restrictions of the same ambient polymer system
before their extensive parts cancel. -/
theorem restrictedWeightedPartition_inter_div_eq_exp
    {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {w : GaugeConfig d N G → ConcretePlaquette d N → ℝ}
    (hloc : IsLocalWeight (d := d) (N := N) (G := G) w)
    (hmeas : ∀ p : ConcretePlaquette d N,
      Measurable (fun A : GaugeConfig d N G => w A p))
    {δ : ℝ} (hbd : ∀ A p, |w A p| ≤ δ)
    {a : (weightedLatticePolymerSystem (d := d) (N := N) μ w).Polymer → ℝ}
    (hkp : KP.KPCriterion
      (weightedLatticePolymerSystem (d := d) (N := N) μ w) a)
    (F Q : Finset (ConcretePlaquette d N)) :
    ((∫ A, ∏ p ∈ F ∩ Q, ((1 : ℂ) + (w A p : ℂ))
        ∂(gaugeMeasureFrom (d := d) (N := N) μ)) /
      (∫ A, ∏ p ∈ Q, ((1 : ℂ) + (w A p : ℂ))
        ∂(gaugeMeasureFrom (d := d) (N := N) μ)))
      =
    Complex.exp (
      KP.clusterSum
        ((weightedLatticePolymerSystem (d := d) (N := N) μ w).restrict
          (Finset.univ.filter (fun c => c.1 ⊆ F ∩ Q)))
      -
      KP.clusterSum
        ((weightedLatticePolymerSystem (d := d) (N := N) μ w).restrict
          (Finset.univ.filter (fun c => c.1 ⊆ Q)))) := by
  let P := weightedLatticePolymerSystem (d := d) (N := N) μ w
  let ΛFQ : Finset P.Polymer :=
    Finset.univ.filter (fun c => c.1 ⊆ F ∩ Q)
  let ΛQ : Finset P.Polymer :=
    Finset.univ.filter (fun c => c.1 ⊆ Q)
  have hnum :
      ∫ A, ∏ p ∈ F ∩ Q, ((1 : ℂ) + (w A p : ℂ))
          ∂(gaugeMeasureFrom (d := d) (N := N) μ)
        = Complex.exp (KP.clusterSum (P.restrict ΛFQ)) := by
    calc
      (∫ A, ∏ p ∈ F ∩ Q, ((1 : ℂ) + (w A p : ℂ))
          ∂(gaugeMeasureFrom (d := d) (N := N) μ))
          =
        ((∫ A, ∏ p ∈ F ∩ Q, (1 + w A p)
            ∂(gaugeMeasureFrom (d := d) (N := N) μ) : ℝ) : ℂ) :=
              integral_prod_one_add_ofReal μ w (F ∩ Q)
      _ = KP.partition P ΛFQ :=
        restricted_weightedPartition_eq_partition μ hloc hmeas hbd (F ∩ Q)
      _ = Complex.exp (KP.clusterSum (P.restrict ΛFQ)) :=
        KP.partition_eq_exp_clusterSum_restrict hkp ΛFQ
  have hden :
      ∫ A, ∏ p ∈ Q, ((1 : ℂ) + (w A p : ℂ))
          ∂(gaugeMeasureFrom (d := d) (N := N) μ)
        = Complex.exp (KP.clusterSum (P.restrict ΛQ)) := by
    calc
      (∫ A, ∏ p ∈ Q, ((1 : ℂ) + (w A p : ℂ))
          ∂(gaugeMeasureFrom (d := d) (N := N) μ))
          =
        ((∫ A, ∏ p ∈ Q, (1 + w A p)
            ∂(gaugeMeasureFrom (d := d) (N := N) μ) : ℝ) : ℂ) :=
              integral_prod_one_add_ofReal μ w Q
      _ = KP.partition P ΛQ :=
        restricted_weightedPartition_eq_partition μ hloc hmeas hbd Q
      _ = Complex.exp (KP.clusterSum (P.restrict ΛQ)) :=
        KP.partition_eq_exp_clusterSum_restrict hkp ΛQ
  rw [hnum, hden]
  exact (Complex.exp_sub _ _).symm

/-- The seam-deleted weighted partition is the ordinary Wilson product
integrated over the retained plaquette region, now as a complex integral. -/
theorem freeBoundaryWeightedPartition_eq_regionIntegral
    {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ) :
    (weightedPartition (d := d) (N := N) μ
      (FreeBoundary.freeBoundaryPlaquetteWeight pe β) : ℂ)
      =
    ∫ A, ∏ p ∈ FreeBoundary.freeBoundaryPlaquettes (d := d) (N := N),
        ((1 : ℂ) + (plaquetteWeight pe β A p : ℂ))
      ∂(gaugeMeasureFrom (d := d) (N := N) μ) := by
  calc
    (weightedPartition (d := d) (N := N) μ
        (FreeBoundary.freeBoundaryPlaquetteWeight pe β) : ℂ)
        =
      ((∫ A, ∏ p ∈ FreeBoundary.freeBoundaryPlaquettes
          (d := d) (N := N), (1 + plaquetteWeight pe β A p)
        ∂(gaugeMeasureFrom (d := d) (N := N) μ) : ℝ) : ℂ) := by
          unfold weightedPartition
          congr 1
          apply integral_congr_ae
          filter_upwards with A
          exact
            FreeBoundary.prod_one_add_freeBoundaryPlaquetteWeight pe β A
    _ = _ := (integral_prod_one_add_ofReal μ
      (fun A p => plaquetteWeight pe β A p)
      (FreeBoundary.freeBoundaryPlaquettes
        (d := d) (N := N))).symm

/-- A free-boundary marked integral agrees with the periodic marked integral
when the marked plaquettes are retained. -/
theorem freeMarkedIntegral_eq_periodic_of_subset
    {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (F : GaugeConfig d N G → ℂ)
    {S₀ : Finset (ConcretePlaquette d N)}
    (hS₀ : S₀ ⊆
      FreeBoundary.freeBoundaryPlaquettes (d := d) (N := N)) :
    (∫ A, F A * ∏ p ∈ S₀,
        (FreeBoundary.freeBoundaryPlaquetteWeight pe β A p : ℂ)
      ∂(gaugeMeasureFrom (d := d) (N := N) μ))
      =
    ∫ A, F A * ∏ p ∈ S₀, (plaquetteWeight pe β A p : ℂ)
      ∂(gaugeMeasureFrom (d := d) (N := N) μ) := by
  apply integral_congr_ae
  filter_upwards with A
  congr 1
  have h := congrArg (fun x : ℝ => (x : ℂ))
    (FreeBoundary.prod_freeBoundaryPlaquetteWeight_eq_of_subset
      pe β A hS₀)
  push_cast at h
  exact h

/-- A free-boundary marked integral vanishes when its marked set contains a
deleted plaquette. -/
theorem freeMarkedIntegral_eq_zero_of_not_subset
    {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (F : GaugeConfig d N G → ℂ)
    {S₀ : Finset (ConcretePlaquette d N)}
    (hS₀ : ¬ S₀ ⊆
      FreeBoundary.freeBoundaryPlaquettes (d := d) (N := N)) :
    (∫ A, F A * ∏ p ∈ S₀,
        (FreeBoundary.freeBoundaryPlaquetteWeight pe β A p : ℂ)
      ∂(gaugeMeasureFrom (d := d) (N := N) μ)) = 0 := by
  have hzero : ∀ A : GaugeConfig d N G,
      F A * ∏ p ∈ S₀,
        (FreeBoundary.freeBoundaryPlaquetteWeight pe β A p : ℂ) = 0 := by
    intro A
    have h := congrArg (fun x : ℝ => (x : ℂ))
      (FreeBoundary.prod_freeBoundaryPlaquetteWeight_eq_zero_of_not_subset
        pe β A hS₀)
    push_cast at h
    rw [h, mul_zero]
  rw [show (fun A : GaugeConfig d N G =>
      F A * ∏ p ∈ S₀,
        (FreeBoundary.freeBoundaryPlaquetteWeight pe β A p : ℂ))
      = fun _ => 0 from funext hzero]
  simp

/-- The far free-boundary product is the periodic product over the
intersection of the far region with the free box. -/
theorem freeFarIntegral_eq_inter
    {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (F : Finset (ConcretePlaquette d N)) :
    (∫ A, ∏ p ∈ F,
        ((1 : ℂ) +
          (FreeBoundary.freeBoundaryPlaquetteWeight pe β A p : ℂ))
      ∂(gaugeMeasureFrom (d := d) (N := N) μ))
      =
    ∫ A, ∏ p ∈ F ∩
        FreeBoundary.freeBoundaryPlaquettes (d := d) (N := N),
        ((1 : ℂ) + (plaquetteWeight pe β A p : ℂ))
      ∂(gaugeMeasureFrom (d := d) (N := N) μ) := by
  apply integral_congr_ae
  filter_upwards with A
  have h := congrArg (fun x : ℝ => (x : ℂ))
    (FreeBoundary.prod_one_add_freeBoundaryPlaquetteWeight_eq_inter
      pe β A F)
  push_cast at h
  exact h

/-- **Exact one-volume marked cluster formula for the genuine free box.**

The marked activity is the ordinary periodic activity whenever its marked
plaquettes are retained, and is zero otherwise.  The remaining ratio is a
difference of two restrictions of the original Wilson polymer system. -/
theorem freeBoundaryLocalGibbsExpectation_eq_markedClusterSum
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (hvol : O.minVolume ≤ n)
    {a : (weightedLatticePolymerSystem (d := d) (N := n + 1) μ
      (fun A p => plaquetteWeight pe β A p)).Polymer → ℝ}
    (hkp : KP.KPCriterion
      (weightedLatticePolymerSystem (d := d) (N := n + 1) μ
        (fun A p => plaquetteWeight pe β A p)) a) :
    (FreeBoundary.freeBoundaryExpectation (d := d) (N := n + 1)
      μ pe β (O.realize n) : ℂ)
      =
    ∑ S₀ ∈ (Finset.univ :
        Finset (ConcretePlaquette d (n + 1))).powerset.filter
        (fun S₀ => localNear (O.realizedSupport n hvol) S₀ = S₀),
      if hS₀ : S₀ ⊆ FreeBoundary.freeBoundaryPlaquettes
          (d := d) (N := n + 1) then
        (∫ A, (O.realize n A : ℂ) *
            ∏ p ∈ S₀, (plaquetteWeight pe β A p : ℂ)
          ∂(gaugeMeasureFrom (d := d) (N := n + 1) μ)) *
        Complex.exp (
          KP.clusterSum
            ((weightedLatticePolymerSystem
              (d := d) (N := n + 1) μ
              (fun A p => plaquetteWeight pe β A p)).restrict
              (Finset.univ.filter (fun c =>
                c.1 ⊆ localFarRegion
                    (O.realizedSupport n hvol) S₀ ∩
                  FreeBoundary.freeBoundaryPlaquettes
                    (d := d) (N := n + 1))))
          -
          KP.clusterSum
            ((weightedLatticePolymerSystem
              (d := d) (N := n + 1) μ
              (fun A p => plaquetteWeight pe β A p)).restrict
              (Finset.univ.filter (fun c =>
                c.1 ⊆ FreeBoundary.freeBoundaryPlaquettes
                  (d := d) (N := n + 1)))))
      else 0 := by
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
  change
    (freeBoundaryLocalGibbsExpectation μ pe β O n : ℂ) = _
  rw [freeBoundaryLocalGibbsExpectation_eq_markedSum_div
    μ hpe_meas hpe β O n hvol, Finset.sum_div]
  refine Finset.sum_congr rfl fun S₀ hS₀mem => ?_
  by_cases hS₀ : S₀ ⊆ FreeBoundary.freeBoundaryPlaquettes
      (d := d) (N := n + 1)
  · rw [dif_pos hS₀, mul_div_assoc,
      freeMarkedIntegral_eq_periodic_of_subset
        μ pe β (fun A => (O.realize n A : ℂ)) hS₀,
      freeFarIntegral_eq_inter μ pe β
        (localFarRegion (O.realizedSupport n hvol) S₀),
      freeBoundaryWeightedPartition_eq_regionIntegral μ pe β]
    congr 1
    exact restrictedWeightedPartition_inter_div_eq_exp μ
      (isLocalWeight_plaquetteWeight pe β) hmeas hδ hkp
      (localFarRegion (O.realizedSupport n hvol) S₀)
      (FreeBoundary.freeBoundaryPlaquettes (d := d) (N := n + 1))
  · rw [dif_neg hS₀,
      freeMarkedIntegral_eq_zero_of_not_subset
        μ pe β (fun A => (O.realize n A : ℂ)) hS₀,
      zero_mul, zero_div]

/-- One summand of the exact normalized marked expansion for the genuine
free box.  A marked set using a deleted plaquette contributes zero. -/
noncomputable def freeLocalMarkedClusterTerm
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (SF : Finset (PosEdge d (n + 1)))
    (S₀ : Finset (ConcretePlaquette d (n + 1))) : ℂ :=
  if S₀ ⊆ FreeBoundary.freeBoundaryPlaquettes
      (d := d) (N := n + 1) then
    (∫ A, (O.realize n A : ℂ) *
        ∏ p ∈ S₀, (plaquetteWeight pe β A p : ℂ)
      ∂(gaugeMeasureFrom (d := d) (N := n + 1) μ)) *
    Complex.exp (
      KP.clusterSum
        ((connectedLatticePolymerSystem
          (d := d) (N := n + 1) μ pe β).restrict
          (Finset.univ.filter (fun c =>
            c.1 ⊆ localFarRegion SF S₀ ∩
              FreeBoundary.freeBoundaryPlaquettes
                (d := d) (N := n + 1))))
      -
      KP.clusterSum
        ((connectedLatticePolymerSystem
          (d := d) (N := n + 1) μ pe β).restrict
          (Finset.univ.filter (fun c =>
            c.1 ⊆ FreeBoundary.freeBoundaryPlaquettes
              (d := d) (N := n + 1)))))
  else 0

/-- The genuine free-boundary expectation is exactly the finite sum of its
normalized free marked terms. -/
theorem freeBoundaryLocalGibbsExpectation_eq_freeLocalMarkedClusterSum
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (hvol : O.minVolume ≤ n)
    {a : (connectedLatticePolymerSystem
      (d := d) (N := n + 1) μ pe β).Polymer → ℝ}
    (hkp : KP.KPCriterion
      (connectedLatticePolymerSystem
        (d := d) (N := n + 1) μ pe β) a) :
    (FreeBoundary.freeBoundaryExpectation (d := d) (N := n + 1)
      μ pe β (O.realize n) : ℂ)
      =
    ∑ S₀ ∈ (Finset.univ :
        Finset (ConcretePlaquette d (n + 1))).powerset.filter
        (fun S₀ => localNear (O.realizedSupport n hvol) S₀ = S₀),
      freeLocalMarkedClusterTerm μ pe β O
        (O.realizedSupport n hvol) S₀ := by
  simpa [freeLocalMarkedClusterTerm,
    weightedLatticePolymerSystem_plaquetteWeight] using
    (freeBoundaryLocalGibbsExpectation_eq_markedClusterSum
      μ hpe_meas hpe β O hvol hkp)

/-- Below-cutoff part of the exact genuine free-boundary marked sum. -/
noncomputable def freeLocalMarkedClusterSmallSum
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (SF : Finset (PosEdge d (n + 1))) (L : ℕ) : ℂ :=
  ∑ S₀ ∈ (Finset.univ :
      Finset (ConcretePlaquette d (n + 1))).powerset.filter
      (fun S₀ => localNear SF S₀ = S₀ ∧ S₀.card < L),
    freeLocalMarkedClusterTerm μ pe β O SF S₀

/-- Norm majorant for the above-cutoff part of the genuine free marked
sum. -/
noncomputable def freeLocalMarkedClusterTailNorm
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (SF : Finset (PosEdge d (n + 1))) (L : ℕ) : ℝ :=
  ∑ S₀ ∈ (Finset.univ :
      Finset (ConcretePlaquette d (n + 1))).powerset.filter
      (fun S₀ => localNear SF S₀ = S₀ ∧ L ≤ S₀.card),
    ‖freeLocalMarkedClusterTerm μ pe β O SF S₀‖

/-- Intersecting two carrier restrictions is the carrier restriction to the
intersection of the two plaquette regions. -/
theorem restrictionInter_weightedPolymer_eq_inter
    {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G)
    (w : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    (F Q : Finset (ConcretePlaquette d N)) :
    KP.restrictionInter
      (weightedLatticePolymerSystem (d := d) (N := N) μ w)
      (Finset.univ.filter (fun c => c.1 ⊆ F))
      (Finset.univ.filter (fun c => c.1 ⊆ Q))
      =
    Finset.univ.filter (fun c => c.1 ⊆ F ∩ Q) := by
  ext c
  simp only [KP.restrictionInter, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨hF, hQ⟩ p hp
    exact Finset.mem_inter.mpr ⟨hF hp, hQ hp⟩
  · intro h
    exact ⟨fun p hp => (Finset.mem_inter.mp (h hp)).1,
      fun p hp => (Finset.mem_inter.mp (h hp)).2⟩

/-- The order-`r+1` cluster correction which simultaneously leaves the
marked far region and the standard free box. -/
noncomputable def freeBoundaryCorrectionSeriesTerm
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G) (R : ℕ)
    (hC : (O.center (R + 2)).minVolume ≤ n)
    (S₀ : Finset (ConcretePlaquette d (n + 1))) (r : ℕ) : ℂ :=
  let P := connectedLatticePolymerSystem
    (d := d) (N := n + 1) μ pe β
  let Λfar : Finset P.Polymer := Finset.univ.filter (fun c =>
    c.1 ⊆ localFarRegion
      ((O.center (R + 2)).realizedSupport n hC) S₀)
  let Λfree : Finset P.Polymer := Finset.univ.filter (fun c =>
    c.1 ⊆ FreeBoundary.freeBoundaryPlaquettes (d := d) (N := n + 1))
  KP.filteredClusterSeriesTerm P
    (fun _ X => ((¬ ∀ i, X i ∈ Λfar) ∧
      (¬ ∀ i, X i ∈ Λfree)) ∧ KP.IsCluster P X) r

/-- The order-`r+1` normalized local correction inside the free box. -/
noncomputable def freeLocalCorrectionSeriesTerm
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (SF : Finset (PosEdge d (n + 1)))
    (S₀ : Finset (ConcretePlaquette d (n + 1))) (r : ℕ) : ℂ :=
  let P := connectedLatticePolymerSystem
    (d := d) (N := n + 1) μ pe β
  let Λfar : Finset P.Polymer := Finset.univ.filter (fun c =>
    c.1 ⊆ localFarRegion SF S₀)
  let Λfree : Finset P.Polymer := Finset.univ.filter (fun c =>
    c.1 ⊆ FreeBoundary.freeBoundaryPlaquettes (d := d) (N := n + 1))
  KP.filteredClusterSeriesTerm P
    (fun _ X => ((∀ i, X i ∈ Λfree) ∧
      (¬ ∀ i, X i ∈ Λfar)) ∧ KP.IsCluster P X) r

/-- The free normalized correction is exactly its ambient filtered series. -/
theorem freeLocalCorrection_eq_series
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (SF : Finset (PosEdge d (n + 1)))
    (S₀ : Finset (ConcretePlaquette d (n + 1)))
    {a : (connectedLatticePolymerSystem
      (d := d) (N := n + 1) μ pe β).Polymer → ℝ}
    (hkp : KP.KPCriterion
      (connectedLatticePolymerSystem
        (d := d) (N := n + 1) μ pe β) a) :
    let P := connectedLatticePolymerSystem
      (d := d) (N := n + 1) μ pe β
    let F := localFarRegion SF S₀
    let Q := FreeBoundary.freeBoundaryPlaquettes
      (d := d) (N := n + 1)
    KP.clusterSum (P.restrict
        (Finset.univ.filter (fun c => c.1 ⊆ Q))) -
      KP.clusterSum (P.restrict
        (Finset.univ.filter (fun c => c.1 ⊆ F ∩ Q)))
      =
    ∑' r, freeLocalCorrectionSeriesTerm
      μ pe β SF S₀ r := by
  dsimp only
  let P := connectedLatticePolymerSystem
    (d := d) (N := n + 1) μ pe β
  let F := localFarRegion SF S₀
  let Q := FreeBoundary.freeBoundaryPlaquettes
    (d := d) (N := n + 1)
  let Λfar : Finset P.Polymer :=
    Finset.univ.filter (fun c => c.1 ⊆ F)
  let Λfree : Finset P.Polymer :=
    Finset.univ.filter (fun c => c.1 ⊆ Q)
  have h := KP.clusterSum_restrict_sub_inter_eq
    P hkp Λfar Λfree
  have hinter :
      KP.restrictionInter P Λfar Λfree =
        Finset.univ.filter (fun c => c.1 ⊆ F ∩ Q) := by
    simpa [P, Λfar, Λfree] using
      (restrictionInter_weightedPolymer_eq_inter
        μ (fun A p => plaquetteWeight pe β A p) F Q)
  rw [hinter] at h
  simpa [freeLocalCorrectionSeriesTerm, P, F, Q, Λfar, Λfree,
    weightedLatticePolymerSystem_plaquetteWeight] using h

/-- Each free local-correction layer is dominated by the ordinary rooted
local tail at cutoff zero. -/
theorem norm_freeLocalCorrectionSeriesTerm_le_localTail
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (SF : Finset (PosEdge d (n + 1)))
    (S₀ : Finset (ConcretePlaquette d (n + 1))) (r : ℕ) :
    ‖freeLocalCorrectionSeriesTerm μ pe β SF S₀ r‖
      ≤
    localCorrectionTailLayer μ pe β
      (SF ∪ S₀.biUnion plaquetteSupport) 0 r := by
  classical
  let P := connectedLatticePolymerSystem
    (d := d) (N := n + 1) μ pe β
  let Λfar : Finset P.Polymer := Finset.univ.filter (fun c =>
    c.1 ⊆ localFarRegion SF S₀)
  let Λfree : Finset P.Polymer := Finset.univ.filter (fun c =>
    c.1 ⊆ FreeBoundary.freeBoundaryPlaquettes (d := d) (N := n + 1))
  let selected : (Fin (r + 1) → P.Polymer) → Prop :=
    fun X => ((∀ i, X i ∈ Λfree) ∧
      (¬ ∀ i, X i ∈ Λfar)) ∧ KP.IsCluster P X
  let tail : (Fin (r + 1) → P.Polymer) → Prop :=
    fun X => (∃ i, ¬ Disjoint (X i).1
      (supportPlaquettes (SF ∪ S₀.biUnion plaquetteSupport))) ∧
      0 ≤ ∑ i, (X i).1.card
  have hsubset :
      (Finset.univ :
        Finset (Fin (r + 1) → P.Polymer)).filter selected
        ⊆
      (Finset.univ :
        Finset (Fin (r + 1) → P.Polymer)).filter tail := by
    intro X hX
    rw [Finset.mem_filter] at hX ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hX.2 with ⟨⟨_, hfar⟩, _⟩
    push_neg at hfar
    obtain ⟨i, hiFar⟩ := hfar
    refine ⟨⟨i, ?_⟩, Nat.zero_le _⟩
    exact
      (not_subset_localFarRegion_iff_not_disjoint_supportPlaquettes
        (SF := SF) (S₀ := S₀) (c := (X i).1)).mp
        (by simpa [Λfar] using hiFar)
  dsimp only [freeLocalCorrectionSeriesTerm,
    KP.filteredClusterSeriesTerm, localCorrectionTailLayer]
  dsimp only [selected, tail, Λfar, Λfree, P] at hsubset
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun X _ => ?_))
    (Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro X hX
        have hX' : X ∈ (Finset.univ :
            Finset (Fin (r + 1) → P.Polymer)).filter selected := by
          simpa [selected, Λfar, Λfree, P] using hX
        have hY := hsubset hX'
        simpa [tail, P] using hY)
      (fun _ _ _ => by positivity))
  rw [norm_mul, norm_prod]
  rw [show ((KP.ursell P X : ℤ) : ℂ) =
      (((KP.ursell P X : ℤ) : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_real, Real.norm_eq_abs]

/-- Summability and the uniform norm bound for the normalized correction
inside the free box. -/
theorem freeLocalCorrectionSeries_summable_volumeUniform
    {d n : ℕ} [NeZero d]
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
          ((Real.exp (|β| * B) - 1) *
            Real.exp (t + ε + 1)))) ≤ t)
    (SF : Finset (PosEdge d (n + 1)))
    (S₀ : Finset (ConcretePlaquette d (n + 1))) :
    Summable (fun r =>
      freeLocalCorrectionSeriesTerm μ pe β SF S₀ r) ∧
    ‖∑' r, freeLocalCorrectionSeriesTerm μ pe β SF S₀ r‖
      ≤
    (2 * t) *
      (((SF.card + 4 * S₀.card : ℕ) : ℝ) * (4 * (d : ℝ))) := by
  let U := SF ∪ S₀.biUnion plaquetteSupport
  have htail := localCorrectionTail_summable_volumeUniform
    μ hpe β t ε ht0 hε0 hr₀ hsmall₀ hr₁ hsmall₁ U 0
  have hnorm : Summable (fun r =>
      ‖freeLocalCorrectionSeriesTerm μ pe β SF S₀ r‖) :=
    Summable.of_nonneg_of_le
      (fun r => norm_nonneg _)
      (fun r => norm_freeLocalCorrectionSeriesTerm_le_localTail
        μ pe β SF S₀ r)
      htail.1
  have hcomplex : Summable (fun r =>
      freeLocalCorrectionSeriesTerm μ pe β SF S₀ r) :=
    Summable.of_norm hnorm
  refine ⟨hcomplex, ?_⟩
  have hcard :
      (U.card : ℝ) ≤ ((SF.card + 4 * S₀.card : ℕ) : ℝ) := by
    exact_mod_cast card_union_biUnion_plaquetteSupport_le SF S₀
  have hfactor : 0 ≤ (2 * t) * (4 * (d : ℝ)) := by positivity
  calc
    ‖∑' r, freeLocalCorrectionSeriesTerm μ pe β SF S₀ r‖
        ≤ ∑' r, ‖freeLocalCorrectionSeriesTerm μ pe β SF S₀ r‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' r, localCorrectionTailLayer μ pe β U 0 r :=
      hnorm.tsum_le_tsum
        (fun r => norm_freeLocalCorrectionSeriesTerm_le_localTail
          μ pe β SF S₀ r)
        htail.1
    _ ≤ Real.exp (-(ε * 0)) *
        ((2 * t) * ((U.card : ℝ) * (4 * (d : ℝ)))) := by
      simpa using htail.2
    _ = (U.card : ℝ) * ((2 * t) * (4 * (d : ℝ))) := by
      simp [Real.exp_zero]
      ring
    _ ≤ ((SF.card + 4 * S₀.card : ℕ) : ℝ) *
        ((2 * t) * (4 * (d : ℝ))) :=
      mul_le_mul_of_nonneg_right hcard hfactor
    _ = (2 * t) *
        (((SF.card + 4 * S₀.card : ℕ) : ℝ) *
          (4 * (d : ℝ))) := by ring

/-- Uniform exponential bound for the normalized free-box correction. -/
theorem norm_exp_freeLocalClusterDiff_le_volumeUniform
    {d n : ℕ} [NeZero d]
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
          ((Real.exp (|β| * B) - 1) *
            Real.exp (t + ε + 1)))) ≤ t)
    (SF : Finset (PosEdge d (n + 1)))
    (S₀ : Finset (ConcretePlaquette d (n + 1)))
    {a : (connectedLatticePolymerSystem
      (d := d) (N := n + 1) μ pe β).Polymer → ℝ}
    (hkp : KP.KPCriterion
      (connectedLatticePolymerSystem
        (d := d) (N := n + 1) μ pe β) a) :
    ‖Complex.exp (
      KP.clusterSum
        ((connectedLatticePolymerSystem
          (d := d) (N := n + 1) μ pe β).restrict
          (Finset.univ.filter (fun c =>
            c.1 ⊆ localFarRegion SF S₀ ∩
              FreeBoundary.freeBoundaryPlaquettes
                (d := d) (N := n + 1))))
      -
      KP.clusterSum
        ((connectedLatticePolymerSystem
          (d := d) (N := n + 1) μ pe β).restrict
          (Finset.univ.filter (fun c =>
            c.1 ⊆ FreeBoundary.freeBoundaryPlaquettes
              (d := d) (N := n + 1)))))‖
      ≤
    Real.exp ((2 * t) *
      (((SF.card + 4 * S₀.card : ℕ) : ℝ) * (4 * (d : ℝ)))) := by
  let corr := ∑' r, freeLocalCorrectionSeriesTerm μ pe β SF S₀ r
  have hcorr := freeLocalCorrection_eq_series
    μ pe β SF S₀ hkp
  have hbound := (freeLocalCorrectionSeries_summable_volumeUniform
    μ hpe β t ε ht0 hε0 hr₀ hsmall₀ hr₁ hsmall₁ SF S₀).2
  have hexponent :
      KP.clusterSum
        ((connectedLatticePolymerSystem
          (d := d) (N := n + 1) μ pe β).restrict
          (Finset.univ.filter (fun c =>
            c.1 ⊆ localFarRegion SF S₀ ∩
              FreeBoundary.freeBoundaryPlaquettes
                (d := d) (N := n + 1))))
      -
      KP.clusterSum
        ((connectedLatticePolymerSystem
          (d := d) (N := n + 1) μ pe β).restrict
          (Finset.univ.filter (fun c =>
            c.1 ⊆ FreeBoundary.freeBoundaryPlaquettes
              (d := d) (N := n + 1))))
        = -corr := by
    dsimp only [corr]
    rw [← hcorr]
    ring
  rw [hexponent]
  calc
    ‖Complex.exp (-corr)‖ ≤ Real.exp ‖-corr‖ :=
      Complex.norm_exp_le_exp_norm _
    _ = Real.exp ‖corr‖ := by rw [norm_neg]
    _ ≤ Real.exp ((2 * t) *
        (((SF.card + 4 * S₀.card : ℕ) : ℝ) *
          (4 * (d : ℝ)))) :=
      Real.exp_le_exp.mpr hbound

/-- Each genuine free-boundary marked term has the same volume-uniform
majorant as the periodic marked term. -/
theorem norm_freeLocalMarkedClusterTerm_le_volumeUniform
    {d n : ℕ} [NeZero d]
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
          ((Real.exp (|β| * B) - 1) *
            Real.exp (t + ε + 1)))) ≤ t)
    (O : CompatibleLocalObservable d G)
    (SF : Finset (PosEdge d (n + 1)))
    (S₀ : Finset (ConcretePlaquette d (n + 1)))
    {a : (connectedLatticePolymerSystem
      (d := d) (N := n + 1) μ pe β).Polymer → ℝ}
    (hkp : KP.KPCriterion
      (connectedLatticePolymerSystem
        (d := d) (N := n + 1) μ pe β) a) :
    ‖freeLocalMarkedClusterTerm μ pe β O SF S₀‖
      ≤ O.bound *
          Real.exp (
            (2 * t) * ((SF.card : ℝ) * (4 * (d : ℝ)))) *
        (localMarkedEffectiveWeight d B β t) ^ S₀.card := by
  classical
  by_cases hS₀ : S₀ ⊆ FreeBoundary.freeBoundaryPlaquettes
      (d := d) (N := n + 1)
  · rw [freeLocalMarkedClusterTerm, if_pos hS₀, norm_mul]
    let δ := Real.exp (|β| * B) - 1
    have hB : 0 ≤ B := le_trans (abs_nonneg _) (hpe 1)
    have hδ : 0 ≤ δ := by
      dsimp only [δ]
      rw [sub_nonneg, ← Real.exp_zero]
      exact Real.exp_le_exp.mpr
        (mul_nonneg (abs_nonneg β) hB)
    have hInt :=
      norm_integral_realize_mul_prod_plaquetteWeight_le
        μ hpe β O S₀
    have hExp :=
      norm_exp_freeLocalClusterDiff_le_volumeUniform
        μ hpe β t ε ht0 hε0 hr₀ hsmall₀ hr₁ hsmall₁
          SF S₀ hkp
    calc
      _ ≤ (O.bound * δ ^ S₀.card) *
          Real.exp (
            (2 * t) *
              (((SF.card + 4 * S₀.card : ℕ) : ℝ) *
                (4 * (d : ℝ)))) := by
        exact mul_le_mul hInt hExp (norm_nonneg _)
          (mul_nonneg O.bound_nonneg (pow_nonneg hδ _))
      _ = O.bound *
          Real.exp (
            (2 * t) * ((SF.card : ℝ) * (4 * (d : ℝ)))) *
          (localMarkedEffectiveWeight d B β t) ^ S₀.card := by
        have hexp :
            Real.exp (
                (2 * t) *
                  (((SF.card + 4 * S₀.card : ℕ) : ℝ) *
                    (4 * (d : ℝ))))
              =
            Real.exp (
                (2 * t) * ((SF.card : ℝ) * (4 * (d : ℝ)))) *
              Real.exp (
                (S₀.card : ℝ) *
                  ((2 * t) * (4 * (4 * (d : ℝ))))) := by
          rw [← Real.exp_add]
          congr 1
          push_cast
          ring
        rw [hexp]
        unfold localMarkedEffectiveWeight
        rw [mul_pow, ← Real.exp_nat_mul]
        ring
  · rw [freeLocalMarkedClusterTerm, if_neg hS₀, norm_zero]
    have hB : 0 ≤ B := le_trans (abs_nonneg _) (hpe 1)
    have hδ : 0 ≤ Real.exp (|β| * B) - 1 := by
      rw [sub_nonneg, ← Real.exp_zero]
      exact Real.exp_le_exp.mpr
        (mul_nonneg (abs_nonneg β) hB)
    have hσ : 0 ≤ localMarkedEffectiveWeight d B β t := by
      unfold localMarkedEffectiveWeight
      exact mul_nonneg hδ (Real.exp_pos _).le
    exact mul_nonneg
      (mul_nonneg O.bound_nonneg (Real.exp_pos _).le)
      (pow_nonneg hσ _)

/-- The genuine free expectation differs from its below-cutoff part by at
most the explicit free marked tail norm. -/
theorem norm_freeBoundaryLocalGibbsExpectation_sub_smallSum_le
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (hvol : O.minVolume ≤ n) (L : ℕ)
    {a : (connectedLatticePolymerSystem
      (d := d) (N := n + 1) μ pe β).Polymer → ℝ}
    (hkp : KP.KPCriterion
      (connectedLatticePolymerSystem
        (d := d) (N := n + 1) μ pe β) a) :
    ‖(FreeBoundary.freeBoundaryExpectation (d := d) (N := n + 1)
        μ pe β (O.realize n) : ℂ) -
      freeLocalMarkedClusterSmallSum μ pe β O
        (O.realizedSupport n hvol) L‖
      ≤
    freeLocalMarkedClusterTailNorm μ pe β O
      (O.realizedSupport n hvol) L := by
  classical
  let SF := O.realizedSupport n hvol
  let U := (Finset.univ :
      Finset (ConcretePlaquette d (n + 1))).powerset.filter
      (fun S₀ => localNear SF S₀ = S₀)
  let small : Finset (ConcretePlaquette d (n + 1)) → Prop :=
    fun S₀ => S₀.card < L
  let f : Finset (ConcretePlaquette d (n + 1)) → ℂ :=
    fun S₀ => freeLocalMarkedClusterTerm μ pe β O SF S₀
  have hfull :=
    freeBoundaryLocalGibbsExpectation_eq_freeLocalMarkedClusterSum
      μ hpe_meas hpe β O hvol hkp
  have hpart := Finset.sum_filter_add_sum_filter_not U small f
  have hsplit :
      (∑ S₀ ∈ U, f S₀)
        =
      freeLocalMarkedClusterSmallSum μ pe β O SF L +
        ∑ S₀ ∈ (Finset.univ :
            Finset (ConcretePlaquette d (n + 1))).powerset.filter
            (fun S₀ => localNear SF S₀ = S₀ ∧ L ≤ S₀.card),
          f S₀ := by
    simpa [U, small, f, freeLocalMarkedClusterSmallSum,
      Finset.filter_filter, Nat.not_lt, and_assoc] using hpart.symm
  change ‖(FreeBoundary.freeBoundaryExpectation
      (d := d) (N := n + 1) μ pe β (O.realize n) : ℂ) -
      freeLocalMarkedClusterSmallSum μ pe β O SF L‖ ≤ _
  rw [show (FreeBoundary.freeBoundaryExpectation
      (d := d) (N := n + 1) μ pe β (O.realize n) : ℂ) =
      ∑ S₀ ∈ U, f S₀ by
        simpa [SF, U, f] using hfull,
    hsplit, add_sub_cancel_left]
  unfold freeLocalMarkedClusterTailNorm
  exact norm_sum_le _ _

/-- Uniform outer-tail bound for the genuine free-boundary marked
expansion. -/
theorem freeLocalMarkedClusterTailNorm_le_volumeUniform
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (t ε η : ℝ) (ht0 : 0 ≤ t) (hε0 : 0 ≤ ε) (hη0 : 0 ≤ η)
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
          ((Real.exp (|β| * B) - 1) *
            Real.exp (t + ε + 1)))) ≤ t)
    (O : CompatibleLocalObservable d G)
    (SF : Finset (PosEdge d (n + 1))) (L : ℕ)
    {a : (connectedLatticePolymerSystem
      (d := d) (N := n + 1) μ pe β).Polymer → ℝ}
    (hkp : KP.KPCriterion
      (connectedLatticePolymerSystem
        (d := d) (N := n + 1) μ pe β) a)
    (hrMarked : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      (localMarkedEffectiveWeight d B β t * Real.exp η) < 1) :
    freeLocalMarkedClusterTailNorm μ pe β O SF L
      ≤
    (O.bound *
      Real.exp ((2 * t) * ((SF.card : ℝ) * (4 * (d : ℝ))))) *
      (Real.exp (-(η * L)) *
        Real.exp (
          ((SF.card : ℝ) * (4 * (d : ℝ))) *
            ((localMarkedEffectiveWeight d B β t * Real.exp η) /
              (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
                (localMarkedEffectiveWeight d B β t *
                  Real.exp η))))) := by
  let σ := localMarkedEffectiveWeight d B β t
  let C₀ := O.bound *
    Real.exp ((2 * t) * ((SF.card : ℝ) * (4 * (d : ℝ))))
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hpe 1)
  have hδ : 0 ≤ Real.exp (|β| * B) - 1 := by
    rw [sub_nonneg, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr
      (mul_nonneg (abs_nonneg β) hB)
  have hσ : 0 ≤ σ := by
    dsimp only [σ, localMarkedEffectiveWeight]
    exact mul_nonneg hδ (Real.exp_pos _).le
  have hC₀ : 0 ≤ C₀ := by
    dsimp only [C₀]
    exact mul_nonneg O.bound_nonneg (Real.exp_pos _).le
  have hterm : ∀ S₀,
      ‖freeLocalMarkedClusterTerm μ pe β O SF S₀‖
        ≤ C₀ * σ ^ S₀.card := by
    intro S₀
    simpa [C₀, σ] using
      (norm_freeLocalMarkedClusterTerm_le_volumeUniform
        μ hpe β t ε ht0 hε0 hr₀ hsmall₀ hr₁ hsmall₁
          O SF S₀ hkp)
  have htail := localPinnedSetTailWeight_le_exp_volumeUniform
    SF σ η hσ hη0 L (by simpa [σ] using hrMarked)
  unfold freeLocalMarkedClusterTailNorm
  calc
    (∑ S₀ ∈ (Finset.univ :
        Finset (ConcretePlaquette d (n + 1))).powerset.filter
        (fun S₀ => localNear SF S₀ = S₀ ∧ L ≤ S₀.card),
      ‖freeLocalMarkedClusterTerm μ pe β O SF S₀‖)
        ≤ ∑ S₀ ∈ (Finset.univ :
            Finset (ConcretePlaquette d (n + 1))).powerset.filter
            (fun S₀ => localNear SF S₀ = S₀ ∧ L ≤ S₀.card),
          C₀ * σ ^ S₀.card :=
      Finset.sum_le_sum fun S₀ _ => hterm S₀
    _ = C₀ * localPinnedSetTailWeight SF σ L := by
      unfold localPinnedSetTailWeight
      rw [Finset.mul_sum]
    _ ≤ C₀ * (Real.exp (-(η * L)) *
        Real.exp (
          ((SF.card : ℝ) * (4 * (d : ℝ))) *
            ((σ * Real.exp η) /
              (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
                (σ * Real.exp η))))) :=
      mul_le_mul_of_nonneg_left htail hC₀
    _ = _ := rfl

/-- Exact algebraic identification of the periodic-minus-free local
correction with the support-to-seam cluster series. -/
theorem localFreeBoundaryCorrection_eq_series
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G) (R : ℕ)
    (hC : (O.center (R + 2)).minVolume ≤ n)
    (S₀ : Finset (ConcretePlaquette d (n + 1)))
    {a : (connectedLatticePolymerSystem
      (d := d) (N := n + 1) μ pe β).Polymer → ℝ}
    (hkp : KP.KPCriterion
      (connectedLatticePolymerSystem
        (d := d) (N := n + 1) μ pe β) a) :
    let P := connectedLatticePolymerSystem
      (d := d) (N := n + 1) μ pe β
    let F := localFarRegion
      ((O.center (R + 2)).realizedSupport n hC) S₀
    let Q := FreeBoundary.freeBoundaryPlaquettes
      (d := d) (N := n + 1)
    (KP.clusterSum P -
        KP.clusterSum (P.restrict
          (Finset.univ.filter (fun c => c.1 ⊆ F)))) -
      (KP.clusterSum (P.restrict
          (Finset.univ.filter (fun c => c.1 ⊆ Q))) -
        KP.clusterSum (P.restrict
          (Finset.univ.filter (fun c => c.1 ⊆ F ∩ Q))))
      =
    ∑' r, freeBoundaryCorrectionSeriesTerm
      μ pe β O R hC S₀ r := by
  dsimp only
  let P := connectedLatticePolymerSystem
    (d := d) (N := n + 1) μ pe β
  let F := localFarRegion
    ((O.center (R + 2)).realizedSupport n hC) S₀
  let Q := FreeBoundary.freeBoundaryPlaquettes
    (d := d) (N := n + 1)
  let Λfar : Finset P.Polymer :=
    Finset.univ.filter (fun c => c.1 ⊆ F)
  let Λfree : Finset P.Polymer :=
    Finset.univ.filter (fun c => c.1 ⊆ Q)
  have h := KP.clusterSum_doubleRestriction_eq
    P hkp Λfar Λfree
  have hinter :
      KP.restrictionInter P Λfar Λfree =
        Finset.univ.filter (fun c => c.1 ⊆ F ∩ Q) := by
    simpa [P, Λfar, Λfree] using
      (restrictionInter_weightedPolymer_eq_inter
        μ (fun A p => plaquetteWeight pe β A p) F Q)
  rw [hinter] at h
  simpa [freeBoundaryCorrectionSeriesTerm, P, F, Q, Λfar, Λfree,
    weightedLatticePolymerSystem_plaquetteWeight] using h

/-- **The free-boundary discrepancy is a literal KP size tail, layer by
layer.**  The subset argument uses
`smallCluster_unionMarkedSupport_subset_freeBoundaryPlaquettes`; the
majorant on the right is exactly the one whose summability is ultimately
proved by `connectedLattice_pinned_tail_volumeUniform`. -/
theorem norm_freeBoundaryCorrectionSeriesTerm_le_localTail
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G) (R K L : ℕ)
    (hC : (O.center (R + 2)).minVolume ≤ n)
    (hroom :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    (S₀ : Finset (ConcretePlaquette d (n + 1)))
    (hpin : localNear
      ((O.center (R + 2)).realizedSupport n hC) S₀ = S₀)
    (hcard : S₀.card ≤ K)
    (hres : (2 * L + 1) + K ≤ R)
    (r : ℕ) :
    ‖freeBoundaryCorrectionSeriesTerm μ pe β O R hC S₀ r‖
      ≤
    localCorrectionTailLayer μ pe β
      (((O.center (R + 2)).realizedSupport n hC) ∪
        S₀.biUnion plaquetteSupport) L r := by
  classical
  let P := connectedLatticePolymerSystem
    (d := d) (N := n + 1) μ pe β
  let SF := (O.center (R + 2)).realizedSupport n hC
  let Λfar : Finset P.Polymer := Finset.univ.filter (fun c =>
    c.1 ⊆ localFarRegion SF S₀)
  let Λfree : Finset P.Polymer := Finset.univ.filter (fun c =>
    c.1 ⊆ FreeBoundary.freeBoundaryPlaquettes (d := d) (N := n + 1))
  let boundary : (Fin (r + 1) → P.Polymer) → Prop :=
    fun X => ((¬ ∀ i, X i ∈ Λfar) ∧
      (¬ ∀ i, X i ∈ Λfree)) ∧ KP.IsCluster P X
  let tail : (Fin (r + 1) → P.Polymer) → Prop :=
    fun X => (∃ i, ¬ Disjoint (X i).1
      (supportPlaquettes (SF ∪ S₀.biUnion plaquetteSupport))) ∧
      L ≤ ∑ i, (X i).1.card
  have hsubset :
      (Finset.univ :
        Finset (Fin (r + 1) → P.Polymer)).filter boundary
        ⊆
      (Finset.univ :
        Finset (Fin (r + 1) → P.Polymer)).filter tail := by
    intro X hX
    rw [Finset.mem_filter] at hX ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hX.2 with ⟨⟨hfar, hfree⟩, hcluster⟩
    push_neg at hfar hfree
    obtain ⟨i, hiFar⟩ := hfar
    obtain ⟨j, hjFree⟩ := hfree
    have hmeet : ∃ i, ¬ Disjoint (X i).1
        (supportPlaquettes (SF ∪ S₀.biUnion plaquetteSupport)) := by
      refine ⟨i, ?_⟩
      exact
        (not_subset_localFarRegion_iff_not_disjoint_supportPlaquettes
          (SF := SF) (S₀ := S₀) (c := (X i).1)).mp
          (by
            simpa [Λfar] using hiFar)
    refine ⟨hmeet, ?_⟩
    by_contra hsmall
    have hall :=
      smallCluster_unionMarkedSupport_subset_freeBoundaryPlaquettes
        μ (fun A p => plaquetteWeight pe β A p)
        O R K L hC hroom hpin hcard hres
        hcluster hmeet (by omega)
    exact hjFree (by
      simpa [Λfree] using
        (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hall j⟩))
  dsimp only [freeBoundaryCorrectionSeriesTerm,
    KP.filteredClusterSeriesTerm, localCorrectionTailLayer]
  dsimp only [boundary, tail, Λfar, Λfree, SF, P] at hsubset
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun X _ => ?_))
    (Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro X hX
        have hX' : X ∈ (Finset.univ :
            Finset (Fin (r + 1) → P.Polymer)).filter boundary := by
          simpa [boundary, Λfar, Λfree, SF, P] using hX
        have hY := hsubset hX'
        simpa [tail, SF, P] using hY)
      (fun _ _ _ => by positivity))
  rw [norm_mul, norm_prod]
  rw [show ((KP.ursell P X : ℤ) : ℂ) =
      (((KP.ursell P X : ℤ) : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_real, Real.norm_eq_abs]

/-- **Volume-uniform free-boundary correction bound.**

This is the requested boundary estimate.  Its final input is
`localCorrectionTail_summable_volumeUniform`, whose rooted proof invokes
`connectedLattice_pinned_tail_volumeUniform` literally. -/
theorem freeBoundaryCorrectionSeries_summable_volumeUniform
    {d n : ℕ} [NeZero d]
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
          ((Real.exp (|β| * B) - 1) *
            Real.exp (t + ε + 1)))) ≤ t)
    (O : CompatibleLocalObservable d G) (R K L : ℕ)
    (hC : (O.center (R + 2)).minVolume ≤ n)
    (hroom :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    (S₀ : Finset (ConcretePlaquette d (n + 1)))
    (hpin : localNear
      ((O.center (R + 2)).realizedSupport n hC) S₀ = S₀)
    (hcard : S₀.card ≤ K)
    (hres : (2 * L + 1) + K ≤ R) :
    Summable (fun r =>
      freeBoundaryCorrectionSeriesTerm μ pe β O R hC S₀ r) ∧
    ‖∑' r, freeBoundaryCorrectionSeriesTerm μ pe β O R hC S₀ r‖
      ≤
    Real.exp (-(ε * L)) *
      ((2 * t) *
        (((((O.center (R + 2)).realizedSupport n hC) ∪
          S₀.biUnion plaquetteSupport).card : ℝ) *
          (4 * (d : ℝ)))) := by
  let U := ((O.center (R + 2)).realizedSupport n hC) ∪
    S₀.biUnion plaquetteSupport
  have htail := localCorrectionTail_summable_volumeUniform
    μ hpe β t ε ht0 hε0 hr₀ hsmall₀ hr₁ hsmall₁ U L
  have hnorm : Summable (fun r =>
      ‖freeBoundaryCorrectionSeriesTerm μ pe β O R hC S₀ r‖) :=
    Summable.of_nonneg_of_le
      (fun r => norm_nonneg _)
      (fun r => norm_freeBoundaryCorrectionSeriesTerm_le_localTail
        μ pe β O R K L hC hroom S₀ hpin hcard hres r)
      htail.1
  have hcomplex : Summable (fun r =>
      freeBoundaryCorrectionSeriesTerm μ pe β O R hC S₀ r) :=
    Summable.of_norm hnorm
  refine ⟨hcomplex, ?_⟩
  calc
    ‖∑' r, freeBoundaryCorrectionSeriesTerm μ pe β O R hC S₀ r‖
        ≤ ∑' r,
          ‖freeBoundaryCorrectionSeriesTerm μ pe β O R hC S₀ r‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' r, localCorrectionTailLayer μ pe β U L r :=
      hnorm.tsum_le_tsum
        (fun r => norm_freeBoundaryCorrectionSeriesTerm_le_localTail
          μ pe β O R K L hC hroom S₀ hpin hcard hres r)
        htail.1
    _ ≤ Real.exp (-(ε * L)) *
        ((2 * t) * ((U.card : ℝ) * (4 * (d : ℝ)))) := htail.2
    _ = _ := rfl

/-- Radius-independent majorant for one periodic/free normalization
correction in the below-cutoff marked layer. -/
noncomputable def freeBoundaryCorrectionBound
    {d : ℕ} {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G)
    (t ε : ℝ) (K L : ℕ) : ℝ :=
  Real.exp (-(ε * L)) *
    ((2 * t) *
      (((Fintype.card O.Support + 4 * K : ℕ) : ℝ) *
        (4 * (d : ℝ))))

/-- The support-to-seam correction of every marked set below `K` is bounded
by the same volume-independent quantity. -/
theorem norm_freeBoundaryCorrectionSeries_le_explicit
    {d n : ℕ} [NeZero d]
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
          ((Real.exp (|β| * B) - 1) *
            Real.exp (t + ε + 1)))) ≤ t)
    (O : CompatibleLocalObservable d G) (R K L : ℕ)
    (hC : (O.center (R + 2)).minVolume ≤ n)
    (hroom :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    (S₀ : Finset (ConcretePlaquette d (n + 1)))
    (hpin : localNear
      ((O.center (R + 2)).realizedSupport n hC) S₀ = S₀)
    (hcard : S₀.card ≤ K)
    (hres : (2 * L + 1) + K ≤ R) :
    ‖∑' r, freeBoundaryCorrectionSeriesTerm
        μ pe β O R hC S₀ r‖
      ≤ freeBoundaryCorrectionBound O t ε K L := by
  let SF := (O.center (R + 2)).realizedSupport n hC
  let U := SF ∪ S₀.biUnion plaquetteSupport
  have hraw :=
    (freeBoundaryCorrectionSeries_summable_volumeUniform
      μ hpe β t ε ht0 hε0 hr₀ hsmall₀ hr₁ hsmall₁
        O R K L hC hroom S₀ hpin hcard hres).2
  have hcardU :
      (U.card : ℝ) ≤
        ((Fintype.card O.Support + 4 * K : ℕ) : ℝ) := by
    have hnat :
        U.card ≤ Fintype.card O.Support + 4 * K := by
      calc
        U.card ≤ SF.card + 4 * S₀.card :=
          card_union_biUnion_plaquetteSupport_le SF S₀
        _ ≤ Fintype.card O.Support + 4 * K := by
          have hSF : SF.card = Fintype.card O.Support := by
            dsimp only [SF]
            simpa [CompatibleLocalObservable.card_support_center] using
              (CompatibleLocalObservable.card_realizedSupport
                (O.center (R + 2)) n hC)
          rw [hSF]
          omega
    exact_mod_cast hnat
  have hfactor :
      0 ≤ Real.exp (-(ε * L)) * ((2 * t) * (4 * (d : ℝ))) := by
    positivity
  calc
    ‖∑' r, freeBoundaryCorrectionSeriesTerm μ pe β O R hC S₀ r‖
        ≤ Real.exp (-(ε * L)) *
          ((2 * t) * ((U.card : ℝ) * (4 * (d : ℝ)))) := by
      simpa [U, SF] using hraw
    _ = (U.card : ℝ) *
        (Real.exp (-(ε * L)) * ((2 * t) * (4 * (d : ℝ)))) := by
      ring
    _ ≤ ((Fintype.card O.Support + 4 * K : ℕ) : ℝ) *
        (Real.exp (-(ε * L)) * ((2 * t) * (4 * (d : ℝ)))) :=
      mul_le_mul_of_nonneg_right hcardU hfactor
    _ = freeBoundaryCorrectionBound O t ε K L := by
      unfold freeBoundaryCorrectionBound
      ring

/-- A below-cutoff marked term changes from periodic to genuine free
boundary by at most its ordinary marked majorant times the explicit
support-to-seam tail. -/
theorem norm_localMarkedClusterTerm_sub_free_le_kpUniform
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (κ : UniformLocalKPRegime d B β)
    (O : CompatibleLocalObservable d G)
    (R K L : ℕ)
    (hn : MarkedWindowAdmissible O R n)
    (hres : (2 * L + 1) + K ≤ R)
    (S₀ : Finset (ConcretePlaquette d (n + 1)))
    (hpin : localNear
      ((O.center (R + 2)).realizedSupport n hn.center_le) S₀ = S₀)
    (hcard : S₀.card ≤ K)
    (hboundOne : markedCorrectionCauchyBound
      O κ.t κ.ε K L ≤ 1) :
    ‖localMarkedClusterTerm μ pe β
          (O.center (R + 2))
          ((O.center (R + 2)).realizedSupport n hn.center_le) S₀
      -
      freeLocalMarkedClusterTerm μ pe β
          (O.center (R + 2))
          ((O.center (R + 2)).realizedSupport n hn.center_le) S₀‖
      ≤
    ((O.center (R + 2)).bound *
      Real.exp (
        (2 * κ.t) *
          ((((O.center (R + 2)).realizedSupport
            n hn.center_le).card : ℝ) *
            (4 * (d : ℝ)))) *
      (localMarkedEffectiveWeight d B β κ.t) ^ S₀.card) *
    (2 * markedCorrectionCauchyBound O κ.t κ.ε K L) := by
  classical
  let C := O.center (R + 2)
  let SF := C.realizedSupport n hn.center_le
  let P := connectedLatticePolymerSystem
    (d := d) (N := n + 1) μ pe β
  let F := localFarRegion SF S₀
  let Q := FreeBoundary.freeBoundaryPlaquettes
    (d := d) (N := n + 1)
  let ep : ℂ :=
    KP.clusterSum (P.restrict
      (Finset.univ.filter (fun c => c.1 ⊆ F))) -
      KP.clusterSum P
  let ef : ℂ :=
    KP.clusterSum (P.restrict
      (Finset.univ.filter (fun c => c.1 ⊆ F ∩ Q))) -
      KP.clusterSum (P.restrict
        (Finset.univ.filter (fun c => c.1 ⊆ Q)))
  let corr : ℂ :=
    ∑' r, freeBoundaryCorrectionSeriesTerm
      μ pe β O R hn.center_le S₀ r
  let D := markedCorrectionCauchyBound O κ.t κ.ε K L
  have hKR : K ≤ R := by omega
  have hS₀ : S₀ ⊆ Q := by
    simpa [Q] using
      (markedSet_subset_freeBoundaryPlaquettes
        O R K hn.center_le hn.room hpin hcard hKR)
  have hkp :=
    connectedLatticePolymerSystem_kpCriterion_volumeUniform
      (d := d) (N := n + 1) μ hpe β (κ.t + κ.ε)
        (add_nonneg κ.t_nonneg κ.ε_pos.le) κ.radius_tilt
        (κ.small_tilt.trans
          (le_add_of_nonneg_right κ.ε_pos.le))
  have hcorrEq :
      ep - ef = -corr := by
    have h :=
      localFreeBoundaryCorrection_eq_series
        μ pe β O R hn.center_le S₀ hkp
    dsimp only [ep, ef, corr, P, F, Q, SF, C]
    rw [← h]
    ring
  have hcorr₀ :
      ‖corr‖ ≤ freeBoundaryCorrectionBound
        O κ.t κ.ε K L := by
    simpa [corr] using
      (norm_freeBoundaryCorrectionSeries_le_explicit
        μ hpe β κ.t κ.ε κ.t_nonneg κ.ε_pos.le
          κ.radius_tilt κ.small_tilt κ.radius_unitTilt
          κ.small_unitTilt O R K L hn.center_le hn.room
          S₀ hpin hcard hres)
  have hfreeLeD :
      freeBoundaryCorrectionBound O κ.t κ.ε K L ≤ D := by
    have ht0 : 0 ≤ κ.t := κ.t_nonneg
    have hfree0 :
        0 ≤ freeBoundaryCorrectionBound O κ.t κ.ε K L := by
      unfold freeBoundaryCorrectionBound
      positivity
    dsimp only [D, markedCorrectionCauchyBound,
      freeBoundaryCorrectionBound]
    dsimp only [freeBoundaryCorrectionBound] at hfree0
    nlinarith
  have hcorr : ‖corr‖ ≤ D := hcorr₀.trans hfreeLeD
  have hcorrOne : ‖-corr‖ ≤ 1 := by
    rw [norm_neg]
    exact hcorr.trans hboundOne
  have hExpDiff :
      ‖Complex.exp ep - Complex.exp ef‖
        ≤ ‖Complex.exp ef‖ * (2 * D) := by
    have hep : ep = ef - corr := by
      linear_combination hcorrEq
    have hexp :
        Complex.exp (ef - corr) =
          Complex.exp ef * Complex.exp (-corr) := by
      rw [show ef - corr = ef + (-corr) by ring, Complex.exp_add]
    have hfactor :
        Complex.exp ep - Complex.exp ef =
          Complex.exp ef * (Complex.exp (-corr) - 1) := by
      calc
        Complex.exp ep - Complex.exp ef =
            Complex.exp (ef - corr) - Complex.exp ef := by rw [hep]
        _ = Complex.exp ef * Complex.exp (-corr) -
              Complex.exp ef := by rw [hexp]
        _ = Complex.exp ef * (Complex.exp (-corr) - 1) := by ring
    rw [hfactor, norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    calc
      ‖Complex.exp (-corr) - 1‖ ≤ 2 * ‖-corr‖ :=
        Complex.norm_exp_sub_one_le hcorrOne
      _ = 2 * ‖corr‖ := by rw [norm_neg]
      _ ≤ 2 * D :=
        mul_le_mul_of_nonneg_left hcorr (by positivity)
  let I : ℂ :=
    ∫ A, (C.realize n A : ℂ) *
      ∏ p ∈ S₀, (plaquetteWeight pe β A p : ℂ)
      ∂(gaugeMeasureFrom (d := d) (N := n + 1) μ)
  have hperiodic :
      localMarkedClusterTerm μ pe β C SF S₀ =
        I * Complex.exp ep := by
    rfl
  have hfree :
      freeLocalMarkedClusterTerm μ pe β C SF S₀ =
        I * Complex.exp ef := by
    have hS₀free : S₀ ⊆ FreeBoundary.freeBoundaryPlaquettes
        (d := d) (N := n + 1) := by
      simpa [Q] using hS₀
    rw [freeLocalMarkedClusterTerm, if_pos hS₀free]
  rw [hperiodic, hfree]
  have hfactorTerm :
      I * Complex.exp ep - I * Complex.exp ef =
        I * (Complex.exp ep - Complex.exp ef) := by ring
  rw [hfactorTerm, norm_mul]
  calc
    ‖I‖ * ‖Complex.exp ep - Complex.exp ef‖
        ≤ ‖I‖ * (‖Complex.exp ef‖ * (2 * D)) :=
      mul_le_mul_of_nonneg_left hExpDiff (norm_nonneg I)
    _ = ‖freeLocalMarkedClusterTerm μ pe β C SF S₀‖ *
        (2 * D) := by
      rw [hfree, norm_mul]
      ring
    _ ≤ (C.bound *
          Real.exp (
            (2 * κ.t) * ((SF.card : ℝ) * (4 * (d : ℝ)))) *
          (localMarkedEffectiveWeight d B β κ.t) ^ S₀.card) *
        (2 * D) := by
      apply mul_le_mul_of_nonneg_right
      · exact norm_freeLocalMarkedClusterTerm_le_volumeUniform
          μ hpe β κ.t κ.ε κ.t_nonneg κ.ε_pos.le
            κ.radius_tilt κ.small_tilt κ.radius_unitTilt
            κ.small_unitTilt C SF S₀ hkp
      · dsimp only [D, markedCorrectionCauchyBound]
        have ht0 : 0 ≤ κ.t := κ.t_nonneg
        positivity
    _ = _ := rfl

/-- Centered below-cutoff marked layer for the genuine free box. -/
noncomputable def freeCenteredMarkedClusterSmallLayer
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (R K : ℕ) (hn : MarkedWindowAdmissible O R n) : ℂ :=
  ∑ S₀ : CenteredMarkedSetBelow O R K hn,
    freeLocalMarkedClusterTerm μ pe β
      (O.center (R + 2))
      ((O.center (R + 2)).realizedSupport n hn.center_le)
      S₀.1

/-- The filtered free marked sum is the explicit centered finite layer. -/
theorem freeLocalMarkedClusterSmallSum_eq_centeredLayer
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (R K : ℕ) (hn : MarkedWindowAdmissible O R n) :
    freeLocalMarkedClusterSmallSum μ pe β
        (O.center (R + 2))
        ((O.center (R + 2)).realizedSupport n hn.center_le) K
      =
    freeCenteredMarkedClusterSmallLayer μ pe β O R K hn := by
  classical
  let f : Finset (ConcretePlaquette d (n + 1)) → ℂ :=
    fun S₀ => freeLocalMarkedClusterTerm μ pe β
      (O.center (R + 2))
      ((O.center (R + 2)).realizedSupport n hn.center_le) S₀
  have hsub :=
    Finset.sum_subtype_eq_sum_filter
      (p := fun S₀ : Finset (ConcretePlaquette d (n + 1)) =>
        localNear
            ((O.center (R + 2)).realizedSupport n hn.center_le) S₀
          = S₀ ∧ S₀.card < K)
      (s := Finset.univ) f
  unfold freeLocalMarkedClusterSmallSum
    freeCenteredMarkedClusterSmallLayer
  simpa [CenteredMarkedSetBelow, f] using hsub.symm

/-- Uniform comparison of the complete below-cutoff periodic and genuine
free marked layers. -/
theorem norm_centeredMarkedClusterSmallLayer_sub_free_le_kpUniform
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (κ : UniformLocalKPRegime d B β)
    (O : CompatibleLocalObservable d G)
    (R K L : ℕ)
    (hn : MarkedWindowAdmissible O R n)
    (hres : (2 * L + 1) + K ≤ R)
    (hboundOne : markedCorrectionCauchyBound
      O κ.t κ.ε K L ≤ 1) :
    ‖centeredMarkedClusterSmallLayer μ pe β O R K hn -
      freeCenteredMarkedClusterSmallLayer μ pe β O R K hn‖
      ≤
    markedSmallLayerCauchyBound
      O B β κ.t κ.ε κ.η K L := by
  let σ := localMarkedEffectiveWeight d B β κ.t
  let A := (O.center (R + 2)).bound *
    Real.exp (
      (2 * κ.t) *
        ((((O.center (R + 2)).realizedSupport
          n hn.center_le).card : ℝ) * (4 * (d : ℝ))))
  let D := markedCorrectionCauchyBound O κ.t κ.ε K L
  let E := Real.exp (
    ((Fintype.card O.Support : ℝ) * (4 * (d : ℝ))) *
      ((σ * Real.exp κ.η) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          (σ * Real.exp κ.η))))
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hpe 1)
  have hδ : 0 ≤ Real.exp (|β| * B) - 1 := by
    rw [sub_nonneg, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr
      (mul_nonneg (abs_nonneg β) hB)
  have hσ : 0 ≤ σ := by
    dsimp only [σ, localMarkedEffectiveWeight]
    exact mul_nonneg hδ (Real.exp_pos _).le
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg
      (O.center (R + 2)).bound_nonneg (Real.exp_pos _).le
  have hD : 0 ≤ D := by
    dsimp only [D, markedCorrectionCauchyBound]
    have ht0 : 0 ≤ κ.t := κ.t_nonneg
    positivity
  unfold centeredMarkedClusterSmallLayer
    freeCenteredMarkedClusterSmallLayer
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ S₀ : CenteredMarkedSetBelow O R K hn,
        (localMarkedClusterTerm μ pe β
            (O.center (R + 2))
            ((O.center (R + 2)).realizedSupport n hn.center_le) S₀.1 -
          freeLocalMarkedClusterTerm μ pe β
            (O.center (R + 2))
            ((O.center (R + 2)).realizedSupport n hn.center_le) S₀.1)‖
        ≤ ∑ S₀ : CenteredMarkedSetBelow O R K hn,
          ((A * σ ^ S₀.1.card) * (2 * D)) := by
      refine (norm_sum_le _ _).trans ?_
      apply Finset.sum_le_sum
      intro S₀ _
      simpa [A, D, σ] using
        (norm_localMarkedClusterTerm_sub_free_le_kpUniform
          μ hpe β κ O R K L hn hres S₀.1 S₀.2.1
            (Nat.le_of_lt S₀.2.2) hboundOne)
    _ = (A * (2 * D)) *
        ∑ S₀ : CenteredMarkedSetBelow O R K hn,
          σ ^ S₀.1.card := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S₀ _
      ring
    _ ≤ (A * (2 * D)) * E := by
      apply mul_le_mul_of_nonneg_left
      · exact sum_centeredMarkedSetBelow_pow_le_exp_volumeUniform
          O R K hn σ κ.η hσ κ.η_pos.le
            (by simpa [σ] using κ.marked_radius)
      · exact mul_nonneg hA (mul_nonneg (by positivity) hD)
    _ = markedSmallLayerCauchyBound
        O B β κ.t κ.ε κ.η K L := by
      dsimp only [A, D, E, σ, markedSmallLayerCauchyBound]
      simp only [CompatibleLocalObservable.bound_center,
        CompatibleLocalObservable.card_realizedSupport,
        CompatibleLocalObservable.card_support_center]

/-- The genuine free-boundary expectation is uniformly close to its
below-cutoff marked layer, with the same outer-tail bound as the periodic
expectation. -/
theorem norm_freeBoundaryExpectation_sub_small_le_kpUniform
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (κ : UniformLocalKPRegime d B β)
    (O : CompatibleLocalObservable d G)
    (hvol : O.minVolume ≤ n) (K : ℕ) :
    ‖(FreeBoundary.freeBoundaryExpectation (d := d) (N := n + 1)
        μ pe β (O.realize n) : ℂ) -
      freeLocalMarkedClusterSmallSum μ pe β O
        (O.realizedSupport n hvol) K‖
      ≤ markedOuterTailBound O B β κ.t κ.η K := by
  have hkp :=
    connectedLatticePolymerSystem_kpCriterion_volumeUniform
      (d := d) (N := n + 1) μ hpe β (κ.t + κ.ε)
        (add_nonneg κ.t_nonneg κ.ε_pos.le) κ.radius_tilt
        (κ.small_tilt.trans
          (le_add_of_nonneg_right κ.ε_pos.le))
  have hfirst :=
    norm_freeBoundaryLocalGibbsExpectation_sub_smallSum_le
      μ hpe_meas hpe β O hvol K hkp
  have htail :=
    freeLocalMarkedClusterTailNorm_le_volumeUniform
      μ hpe β κ.t κ.ε κ.η κ.t_nonneg κ.ε_pos.le κ.η_pos.le
        κ.radius_tilt κ.small_tilt κ.radius_unitTilt κ.small_unitTilt
        O (O.realizedSupport n hvol) K hkp κ.marked_radius
  exact hfirst.trans (by
    simpa [markedOuterTailBound,
      CompatibleLocalObservable.card_realizedSupport] using htail)

/-- **Same-volume periodic/free comparison.**

The two genuine Gibbs expectations differ by two outer marked tails and
the support-to-seam correction of the finite below-cutoff layer. -/
theorem norm_localGibbsExpectation_sub_freeBoundary_le_kpUniform
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (κ : UniformLocalKPRegime d B β)
    (O : CompatibleLocalObservable d G)
    (R K L : ℕ)
    (hn : MarkedWindowAdmissible O R n)
    (hres : (2 * L + 1) + K ≤ R)
    (hboundOne : markedCorrectionCauchyBound
      O κ.t κ.ε K L ≤ 1) :
    ‖(localGibbsExpectation μ pe β O n : ℂ) -
      (FreeBoundary.freeBoundaryExpectation (d := d) (N := n + 1)
        μ pe β ((O.center (R + 2)).realize n) : ℂ)‖
      ≤
    2 * markedOuterTailBound O B β κ.t κ.η K +
      markedSmallLayerCauchyBound
        O B β κ.t κ.ε κ.η K L := by
  let C := O.center (R + 2)
  let Sp := centeredMarkedClusterSmallLayer μ pe β O R K hn
  let Sf := freeCenteredMarkedClusterSmallLayer μ pe β O R K hn
  have hpTail₀ :=
    norm_localGibbsExpectation_sub_localMarkedClusterSmallSum_le_volumeUniform
      μ hpe_meas hpe β κ.t κ.ε κ.η
        κ.t_nonneg κ.ε_pos.le κ.η_pos.le
        κ.radius_tilt κ.small_tilt κ.radius_unitTilt κ.small_unitTilt
        C hn.center_le K
        (connectedLatticePolymerSystem_kpCriterion_volumeUniform
          (d := d) (N := n + 1) μ hpe β (κ.t + κ.ε)
            (add_nonneg κ.t_nonneg κ.ε_pos.le) κ.radius_tilt
            (κ.small_tilt.trans
              (le_add_of_nonneg_right κ.ε_pos.le)))
        κ.marked_radius
  have hpTail :
      ‖(localGibbsExpectation μ pe β C n : ℂ) - Sp‖
        ≤ markedOuterTailBound O B β κ.t κ.η K := by
    rw [localMarkedClusterSmallSum_eq_centeredMarkedLayer
      μ pe β O R K hn] at hpTail₀
    simpa [C, Sp, markedOuterTailBound,
      CompatibleLocalObservable.card_support_center] using hpTail₀
  have hfTail₀ :=
    norm_freeBoundaryExpectation_sub_small_le_kpUniform
      μ hpe_meas hpe β κ C hn.center_le K
  have hfTail :
      ‖(FreeBoundary.freeBoundaryExpectation (d := d) (N := n + 1)
          μ pe β (C.realize n) : ℂ) - Sf‖
        ≤ markedOuterTailBound O B β κ.t κ.η K := by
    rw [freeLocalMarkedClusterSmallSum_eq_centeredLayer
      μ pe β O R K hn] at hfTail₀
    simpa [C, Sf, markedOuterTailBound,
      CompatibleLocalObservable.card_support_center] using hfTail₀
  have hsmall :
      ‖Sp - Sf‖ ≤ markedSmallLayerCauchyBound
          O B β κ.t κ.ε κ.η K L :=
    norm_centeredMarkedClusterSmallLayer_sub_free_le_kpUniform
      μ hpe β κ O R K L hn hres hboundOne
  have hcenter :
      localGibbsExpectation μ pe β C n =
        localGibbsExpectation μ pe β O n := by
    simpa [C] using
      (localGibbsExpectation_center
        μ pe β O (R + 2) n hn.center_le)
  rw [← hcenter]
  calc
    ‖(localGibbsExpectation μ pe β C n : ℂ) -
        (FreeBoundary.freeBoundaryExpectation
          (d := d) (N := n + 1) μ pe β (C.realize n) : ℂ)‖
        =
      ‖((localGibbsExpectation μ pe β C n : ℂ) - Sp) +
        (Sp - Sf) +
        (Sf - (FreeBoundary.freeBoundaryExpectation
          (d := d) (N := n + 1) μ pe β (C.realize n) : ℂ))‖ := by
      congr 1
      ring
    _ ≤
        ‖(localGibbsExpectation μ pe β C n : ℂ) - Sp‖ +
        ‖Sp - Sf‖ +
        ‖Sf - (FreeBoundary.freeBoundaryExpectation
          (d := d) (N := n + 1) μ pe β (C.realize n) : ℂ)‖ := by
      calc
        ‖((localGibbsExpectation μ pe β C n : ℂ) - Sp) +
            (Sp - Sf) +
            (Sf - (FreeBoundary.freeBoundaryExpectation
              (d := d) (N := n + 1) μ pe β (C.realize n) : ℂ))‖
            ≤
          ‖((localGibbsExpectation μ pe β C n : ℂ) - Sp) +
            (Sp - Sf)‖ +
          ‖Sf - (FreeBoundary.freeBoundaryExpectation
            (d := d) (N := n + 1) μ pe β (C.realize n) : ℂ)‖ :=
          norm_add_le _ _
        _ ≤
          (‖(localGibbsExpectation μ pe β C n : ℂ) - Sp‖ +
            ‖Sp - Sf‖) +
          ‖Sf - (FreeBoundary.freeBoundaryExpectation
            (d := d) (N := n + 1) μ pe β (C.realize n) : ℂ)‖ :=
          add_le_add (norm_add_le _ _) (le_refl _)
    _ ≤ markedOuterTailBound O B β κ.t κ.η K +
        markedSmallLayerCauchyBound O B β κ.t κ.ε κ.η K L +
        markedOuterTailBound O B β κ.t κ.η K := by
      exact add_le_add (add_le_add hpTail hsmall)
        (by simpa [norm_sub_rev] using hfTail)
    _ = 2 * markedOuterTailBound O B β κ.t κ.η K +
        markedSmallLayerCauchyBound
          O B β κ.t κ.ε κ.η K L := by ring

end WindowPolymer

end YangMills
