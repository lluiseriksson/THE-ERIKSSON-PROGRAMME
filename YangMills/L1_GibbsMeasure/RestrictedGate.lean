/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.L1_GibbsMeasure.PolymerRepresentation
import YangMills.KP.Restriction

/-!
# The region-restricted lattice gate (VU campaign, R3)

`docs/AREA-LAW-VU-PLAN.md` R3, by the TRUNCATION DEVICE: the
region-restricted partition function `Z_F = ∫ ∏_{p∈F}(1+w_p)` is the
FULL weighted partition of the truncated weight `w·1_F`, so the banked
3.2M-heartbeat gate `weightedPartition_eq_partition` applies
unchanged; the truncated gas then collapses onto the `F`-polymers by
`KP.partition_eq_of_activity_eq_zero`.

This file: the truncation substrate — the pointwise identity, the
inherited hypotheses (`IsLocalWeight`, measurability, bound), and the
truncated activities (zero off `F`, agreement on `F`).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills

open MeasureTheory

variable {d N : ℕ} [NeZero d] [NeZero N] {G : Type*} [Group G] [MeasurableSpace G]

open Classical in
/-- The **truncated weight**: `w` on `F`, zero outside. -/
noncomputable def truncWeight
    (w : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    (F : Finset (ConcretePlaquette d N)) :
    GaugeConfig d N G → ConcretePlaquette d N → ℝ :=
  fun A p => if p ∈ F then w A p else 0

open Classical in
/-- (i) The pointwise truncation identity:
`∏_{p∈F}(1+w) = ∏_{p∈univ}(1+w·1_F)`. -/
theorem prod_one_add_truncWeight
    (w : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    (F : Finset (ConcretePlaquette d N)) (A : GaugeConfig d N G) :
    ∏ p ∈ F, (1 + w A p)
      = ∏ p : ConcretePlaquette d N, (1 + truncWeight w F A p) := by
  calc ∏ p ∈ F, (1 + w A p)
      = ∏ p ∈ F, (1 + truncWeight w F A p) :=
        Finset.prod_congr rfl fun p hp => by
          unfold truncWeight
          rw [if_pos hp]
    _ = ∏ p : ConcretePlaquette d N, (1 + truncWeight w F A p) :=
        Finset.prod_subset (Finset.subset_univ F) fun p _ hp => by
          unfold truncWeight
          rw [if_neg hp, add_zero]

open Classical in
/-- The truncated weight is local whenever `w` is. -/
theorem isLocalWeight_truncWeight
    {w : GaugeConfig d N G → ConcretePlaquette d N → ℝ}
    (hloc : IsLocalWeight (d := d) (N := N) (G := G) w)
    (F : Finset (ConcretePlaquette d N)) :
    IsLocalWeight (d := d) (N := N) (G := G) (truncWeight w F) := by
  intro p A A' h
  unfold truncWeight
  by_cases hp : p ∈ F
  · rw [if_pos hp, if_pos hp]
    exact hloc p A A' h
  · rw [if_neg hp, if_neg hp]

open Classical in
/-- The truncated weight is measurable whenever `w` is. -/
theorem measurable_truncWeight
    {w : GaugeConfig d N G → ConcretePlaquette d N → ℝ}
    (hmeas : ∀ p : ConcretePlaquette d N,
      Measurable (fun A : GaugeConfig d N G => w A p))
    (F : Finset (ConcretePlaquette d N)) :
    ∀ p : ConcretePlaquette d N,
      Measurable (fun A : GaugeConfig d N G => truncWeight w F A p) := by
  intro p
  unfold truncWeight
  by_cases hp : p ∈ F
  · simpa [hp] using hmeas p
  · simpa [hp] using measurable_const (a := (0 : ℝ))

open Classical in
/-- The truncated weight inherits the uniform bound. -/
theorem truncWeight_bound
    {w : GaugeConfig d N G → ConcretePlaquette d N → ℝ} {δ : ℝ}
    (hbd : ∀ (A : GaugeConfig d N G) (p : ConcretePlaquette d N),
      |w A p| ≤ δ)
    (F : Finset (ConcretePlaquette d N)) :
    ∀ (A : GaugeConfig d N G) (p : ConcretePlaquette d N),
      |truncWeight w F A p| ≤ δ := by
  intro A p
  unfold truncWeight
  by_cases hp : p ∈ F
  · rw [if_pos hp]
    exact hbd A p
  · rw [if_neg hp, abs_zero]
    exact le_trans (abs_nonneg (w A p)) (hbd A p)

open Classical in
/-- (ii-zero) Truncated activities vanish off the `F`-polymers. -/
theorem truncated_activity_eq_zero
    (μ : Measure G)
    (w : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    (F : Finset (ConcretePlaquette d N))
    (c : (weightedLatticePolymerSystem (d := d) (N := N) μ
      (truncWeight w F)).Polymer)
    (hc : ¬ c.1 ⊆ F) :
    (weightedLatticePolymerSystem (d := d) (N := N) μ
      (truncWeight w F)).activity c = 0 := by
  obtain ⟨p, hpc, hpF⟩ := Finset.not_subset.mp hc
  show ((∫ A, ∏ q ∈ c.1, truncWeight w F A q
      ∂(gaugeMeasureFrom (d := d) (N := N) μ) : ℝ) : ℂ) = 0
  have hzero : ∀ A : GaugeConfig d N G,
      ∏ q ∈ c.1, truncWeight w F A q = 0 := fun A =>
    Finset.prod_eq_zero hpc (by unfold truncWeight; rw [if_neg hpF])
  rw [show (fun A : GaugeConfig d N G =>
      ∏ q ∈ c.1, truncWeight w F A q) = fun _ => (0 : ℝ) from
    funext hzero]
  simp

open Classical in
/-- (ii-agree) Truncated activities agree with the original ones on
the `F`-polymers. -/
theorem truncated_activity_eq
    (μ : Measure G)
    (w : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    (F : Finset (ConcretePlaquette d N))
    (c : (weightedLatticePolymerSystem (d := d) (N := N) μ
      (truncWeight w F)).Polymer)
    (hc : c.1 ⊆ F) :
    (weightedLatticePolymerSystem (d := d) (N := N) μ
        (truncWeight w F)).activity c
      = (weightedLatticePolymerSystem (d := d) (N := N) μ w).activity
          ⟨c.1, c.2⟩ := by
  show ((∫ A, ∏ q ∈ c.1, truncWeight w F A q
      ∂(gaugeMeasureFrom (d := d) (N := N) μ) : ℝ) : ℂ) = _
  have hagree : ∀ A : GaugeConfig d N G,
      ∏ q ∈ c.1, truncWeight w F A q = ∏ q ∈ c.1, w A q := fun A =>
    Finset.prod_congr rfl fun q hq => by
      unfold truncWeight
      rw [if_pos (hc hq)]
  rw [show (fun A : GaugeConfig d N G =>
      ∏ q ∈ c.1, truncWeight w F A q)
    = fun A => ∏ q ∈ c.1, w A q from funext hagree]
  rfl

open Classical in
/-- **R3 — THE REGION-RESTRICTED LATTICE GATE:** the region-restricted
partition function is the polymer partition function over the
`F`-polymers of the ORIGINAL weighted gas:

`∫ ∏_{p∈F}(1+w_p) = Ξ_{gas(w)}(polymersIn F)`.

Proof by the truncation device: truncate the weight, apply the banked
full-volume gate, drop the vanished activities, restore the original
activities on the `F`-polymers. -/
theorem restricted_weightedPartition_eq_partition
    (μ : Measure G) [IsProbabilityMeasure μ]
    {w : GaugeConfig d N G → ConcretePlaquette d N → ℝ}
    (hloc : IsLocalWeight (d := d) (N := N) (G := G) w)
    (hmeas : ∀ p : ConcretePlaquette d N,
      Measurable (fun A : GaugeConfig d N G => w A p))
    {δ : ℝ} (hbd : ∀ A p, |w A p| ≤ δ)
    (F : Finset (ConcretePlaquette d N)) :
    ((∫ A, ∏ p ∈ F, (1 + w A p)
        ∂(gaugeMeasureFrom (d := d) (N := N) μ) : ℝ) : ℂ)
      = KP.partition (weightedLatticePolymerSystem (d := d) (N := N) μ w)
          (Finset.univ.filter (fun c => c.1 ⊆ F)) := by
  calc ((∫ A, ∏ p ∈ F, (1 + w A p)
        ∂(gaugeMeasureFrom (d := d) (N := N) μ) : ℝ) : ℂ)
      = ((weightedPartition (d := d) (N := N) μ
          (truncWeight w F) : ℝ) : ℂ) := by
        unfold weightedPartition
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun A => ?_)
        exact prod_one_add_truncWeight w F A
    _ = KP.partition (weightedLatticePolymerSystem (d := d) (N := N) μ
          (truncWeight w F)) Finset.univ :=
        weightedPartition_eq_partition μ
          (isLocalWeight_truncWeight hloc F)
          (measurable_truncWeight hmeas F)
          (truncWeight_bound hbd F)
    _ = KP.partition (weightedLatticePolymerSystem (d := d) (N := N) μ
          (truncWeight w F))
          (Finset.univ.filter (fun c => c.1 ⊆ F)) :=
        KP.partition_eq_of_activity_eq_zero _ _ fun c hc =>
          truncated_activity_eq_zero μ w F c fun hsub =>
            hc (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsub⟩)
    _ = KP.partition (weightedLatticePolymerSystem (d := d) (N := N) μ w)
          (Finset.univ.filter (fun c => c.1 ⊆ F)) := by
        unfold KP.partition
        refine Finset.sum_congr rfl fun S hS => ?_
        refine Finset.prod_congr rfl fun X hX => ?_
        have hXF : X.1 ⊆ F := by
          have hS' := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
          exact (Finset.mem_filter.mp (hS' hX)).2
        exact truncated_activity_eq μ w F X hXF

open Classical in
/-- **The lattice gas satisfies the uniform-scale KP criterion** —
the form `tsum_offRegionClusterWeight_le` consumes: the banked
double-tilt criterion dominates the uniform `e^s` tilt for
`s ≤ 1 + ε` (polymers are nonempty, so `|c| ≥ 1`). -/
theorem weighted_scale_kpCriterion
    (μ : Measure G) [IsProbabilityMeasure μ]
    {w : GaugeConfig d N G → ConcretePlaquette d N → ℝ}
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hbd : ∀ A p, |w A p| ≤ δ)
    (t ε s : ℝ) (ht0 : 0 ≤ t) (hε0 : 0 ≤ ε) (hs : s ≤ 1 + ε)
    (hr : ((16 * d + 1 : ℕ) : ℝ) ^ 2 * (δ * Real.exp (t + ε + 1)) < 1)
    (hsmall : ((16 * d : ℕ) : ℝ) *
      ((δ * Real.exp (t + ε + 1)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          (δ * Real.exp (t + ε + 1)))) ≤ t) :
    KP.KPCriterion
      ((weightedLatticePolymerSystem (d := d) (N := N) μ
          w).scaleActivity (Real.exp s))
      (fun c => t * (c.1.card : ℝ)) := by
  refine KP.KPCriterion.of_activity_norm_le
    (z₂ := fun c : (weightedLatticePolymerSystem (d := d) (N := N) μ
        w).Polymer =>
      ((Real.exp (ε * (c.1.card : ℝ)) : ℝ) : ℂ) *
      (((Real.exp (c.1.card : ℝ) : ℝ) : ℂ) *
        (weightedLatticePolymerSystem (d := d) (N := N) μ
          w).activity c))
    ?_ (weighted_unitTilt_kpCriterion_volumeUniform μ hδ0 hbd t ε
      ht0 hr hsmall)
  intro c
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _),
    abs_of_pos (Real.exp_pos _), ← mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  have hcard : (1 : ℝ) ≤ (c.1.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr c.2.1
  nlinarith [hcard, hs,
    mul_nonneg hε0 (by linarith : (0 : ℝ) ≤ (c.1.card : ℝ) - 1)]

open Classical in
/-- **V1 — THE INSTANTIATED `Z`-RATIO BOUND** (the campaign's center
of mass, assembled): at strong coupling, every region-restricted
lattice partition function is `exp(clusterSum)` of the restricted gas,
and the LOG-RATIO against the full `Z` is bounded by a sum over the
polymers NOT contained in the region — volume-free when the region's
complement is the loop's neighbourhood. -/
theorem restricted_partition_log_ratio_bound
    (μ : Measure G) [IsProbabilityMeasure μ]
    {w : GaugeConfig d N G → ConcretePlaquette d N → ℝ}
    (hloc : IsLocalWeight (d := d) (N := N) (G := G) w)
    (hmeas : ∀ p : ConcretePlaquette d N,
      Measurable (fun A : GaugeConfig d N G => w A p))
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hbd : ∀ A p, |w A p| ≤ δ)
    (t ε : ℝ) (ht0 : 0 ≤ t) (hε0 : 0 ≤ ε)
    (hr : ((16 * d + 1 : ℕ) : ℝ) ^ 2 * (δ * Real.exp (t + ε + 1)) < 1)
    (hsmall : ((16 * d : ℕ) : ℝ) *
      ((δ * Real.exp (t + ε + 1)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          (δ * Real.exp (t + ε + 1)))) ≤ t)
    (F : Finset (ConcretePlaquette d N)) :
    ((∫ A, ∏ p ∈ F, (1 + w A p)
        ∂(gaugeMeasureFrom (d := d) (N := N) μ) : ℝ) : ℂ)
      = Complex.exp (KP.clusterSum
          ((weightedLatticePolymerSystem (d := d) (N := N) μ w).restrict
            (Finset.univ.filter (fun c => c.1 ⊆ F))))
    ∧ ‖KP.clusterSum
          (weightedLatticePolymerSystem (d := d) (N := N) μ w)
        - KP.clusterSum
          ((weightedLatticePolymerSystem (d := d) (N := N) μ w).restrict
            (Finset.univ.filter (fun c => c.1 ⊆ F)))‖
      ≤ ∑ c ∈ (Finset.univ.filter
            (fun c : (weightedLatticePolymerSystem (d := d) (N := N) μ
              w).Polymer => c.1 ⊆ F))ᶜ,
          Real.exp 1 *
            ‖(weightedLatticePolymerSystem (d := d) (N := N) μ
              w).activity c‖ *
            Real.exp (t * (c.1.card : ℝ)) := by
  classical
  have hscale1 := weighted_scale_kpCriterion μ hδ0 hbd t ε 1 ht0 hε0
    (by linarith) hr hsmall
  have hcrit : KP.KPCriterion
      (weightedLatticePolymerSystem (d := d) (N := N) μ w)
      (fun c => t * (c.1.card : ℝ)) := by
    refine KP.KPCriterion.of_activity_norm_le
      (z₂ := fun c : (weightedLatticePolymerSystem (d := d) (N := N) μ
          w).Polymer =>
        ((Real.exp 1 : ℝ) : ℂ) *
          (weightedLatticePolymerSystem (d := d) (N := N) μ
            w).activity c)
      ?_ hscale1
    intro c
    rw [norm_mul]
    refine le_mul_of_one_le_left (norm_nonneg _) ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.one_le_exp (zero_le_one (α := ℝ))
  constructor
  · calc ((∫ A, ∏ p ∈ F, (1 + w A p)
        ∂(gaugeMeasureFrom (d := d) (N := N) μ) : ℝ) : ℂ)
        = KP.partition
            (weightedLatticePolymerSystem (d := d) (N := N) μ w)
            (Finset.univ.filter (fun c => c.1 ⊆ F)) :=
          restricted_weightedPartition_eq_partition μ hloc hmeas hbd F
      _ = Complex.exp (KP.clusterSum
            ((weightedLatticePolymerSystem (d := d) (N := N) μ
              w).restrict
              (Finset.univ.filter (fun c => c.1 ⊆ F)))) :=
          KP.partition_eq_exp_clusterSum_restrict hcrit _
  · refine le_trans (KP.norm_clusterSum_sub_restrict_le _ hcrit _) ?_
    refine le_trans (KP.tsum_offRegionClusterWeight_le _ 1 one_pos
      hscale1 _) (le_of_eq ?_)
    rw [inv_one, one_mul]

open Classical in
/-- **The neighbourhood count (V1 bookkeeping):** the `Z`-ratio
exponent is bounded by `#Fᶜ` times a volume-free constant — every
escaping polymer is charged to a plaquette OUTSIDE `F` it contains,
and the through-plaquette polymer sums are volume-uniform. -/
theorem offRegion_polymer_sum_le
    (μ : Measure G) [IsProbabilityMeasure μ]
    {w : GaugeConfig d N G → ConcretePlaquette d N → ℝ}
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hbd : ∀ A p, |w A p| ≤ δ)
    (t : ℝ) (ht0 : 0 ≤ t)
    (hr : ((16 * d + 1 : ℕ) : ℝ) ^ 2 * (δ * Real.exp t) < 1)
    (F : Finset (ConcretePlaquette d N)) :
    ∑ c ∈ (Finset.univ.filter
        (fun c : (weightedLatticePolymerSystem (d := d) (N := N) μ
          w).Polymer => c.1 ⊆ F))ᶜ,
        Real.exp 1 *
          ‖(weightedLatticePolymerSystem (d := d) (N := N) μ
            w).activity c‖ *
          Real.exp (t * (c.1.card : ℝ))
      ≤ (Fᶜ.card : ℝ) * (Real.exp 1 *
          ((δ * Real.exp t) /
            (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 * (δ * Real.exp t)))) := by
  classical
  set x : ℝ := δ * Real.exp t with hxdef
  have hx0 : (0 : ℝ) ≤ x := mul_nonneg hδ0 (Real.exp_pos t).le
  -- per-polymer: the summand is at most e·x^{|c|}
  have hterm : ∀ c : (weightedLatticePolymerSystem (d := d) (N := N) μ
      w).Polymer,
      Real.exp 1 *
        ‖(weightedLatticePolymerSystem (d := d) (N := N) μ
          w).activity c‖ * Real.exp (t * (c.1.card : ℝ))
      ≤ Real.exp 1 * x ^ c.1.card := by
    intro c
    have h1 := norm_weightedLatticePolymerSystem_activity_le μ hbd c
    have h2 : Real.exp (t * (c.1.card : ℝ))
        = Real.exp t ^ c.1.card := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    calc Real.exp 1 *
        ‖(weightedLatticePolymerSystem (d := d) (N := N) μ
          w).activity c‖ * Real.exp (t * (c.1.card : ℝ))
        ≤ Real.exp 1 * δ ^ c.1.card * Real.exp (t * (c.1.card : ℝ)) := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h1 (Real.exp_pos 1).le)
            (Real.exp_pos _).le
      _ = Real.exp 1 * x ^ c.1.card := by
          rw [h2, hxdef, mul_pow]
          ring
  -- charge each escaping polymer to a plaquette outside F
  calc ∑ c ∈ (Finset.univ.filter
        (fun c : (weightedLatticePolymerSystem (d := d) (N := N) μ
          w).Polymer => c.1 ⊆ F))ᶜ,
        Real.exp 1 *
          ‖(weightedLatticePolymerSystem (d := d) (N := N) μ
            w).activity c‖ *
          Real.exp (t * (c.1.card : ℝ))
      ≤ ∑ c ∈ (Finset.univ.filter
          (fun c : (weightedLatticePolymerSystem (d := d) (N := N) μ
            w).Polymer => c.1 ⊆ F))ᶜ,
          ∑ p ∈ Fᶜ, if p ∈ c.1 then Real.exp 1 * x ^ c.1.card else 0 := by
        refine Finset.sum_le_sum fun c hc => ?_
        have hnc : ¬ c.1 ⊆ F := by
          intro hsub
          rw [Finset.mem_compl, Finset.mem_filter] at hc
          exact hc ⟨Finset.mem_univ _, hsub⟩
        obtain ⟨p, hpc, hpF⟩ := Finset.not_subset.mp hnc
        have hkey : Real.exp 1 *
            ‖(weightedLatticePolymerSystem (d := d) (N := N) μ
              w).activity c‖ * Real.exp (t * (c.1.card : ℝ))
            ≤ if p ∈ c.1 then Real.exp 1 * x ^ c.1.card else 0 := by
          rw [if_pos hpc]
          exact hterm c
        refine le_trans hkey ?_
        refine Finset.single_le_sum
          (f := fun p => if p ∈ c.1 then Real.exp 1 * x ^ c.1.card else 0)
          (fun q _ => ?_) (Finset.mem_compl.mpr hpF)
        show (0 : ℝ) ≤ if q ∈ c.1 then Real.exp 1 * x ^ c.1.card else 0
        split_ifs
        · positivity
        · exact le_rfl
    _ = ∑ p ∈ Fᶜ, ∑ c ∈ (Finset.univ.filter
          (fun c : (weightedLatticePolymerSystem (d := d) (N := N) μ
            w).Polymer => c.1 ⊆ F))ᶜ,
          if p ∈ c.1 then Real.exp 1 * x ^ c.1.card else 0 :=
        Finset.sum_comm
    _ ≤ ∑ p ∈ Fᶜ, ∑ c ∈ (Finset.univ :
          Finset (weightedLatticePolymerSystem (d := d) (N := N) μ
            w).Polymer).filter (fun c => p ∈ c.1),
          Real.exp 1 * x ^ c.1.card := by
        refine Finset.sum_le_sum fun p _ => ?_
        rw [Finset.sum_filter]
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ _) fun c _ _ => ?_
        show (0 : ℝ) ≤ if p ∈ c.1 then Real.exp 1 * x ^ c.1.card else 0
        split_ifs
        · positivity
        · exact le_rfl
    _ ≤ ∑ _p ∈ Fᶜ, Real.exp 1 *
          (x / (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 * x)) := by
        refine Finset.sum_le_sum fun p _ => ?_
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos 1).le
        exact sum_connectedPolymers_through_le (d := d) (N := N) p x hx0 hr
    _ = (Fᶜ.card : ℝ) * (Real.exp 1 *
          (x / (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 * x))) := by
        rw [Finset.sum_const, nsmul_eq_mul]

end YangMills
