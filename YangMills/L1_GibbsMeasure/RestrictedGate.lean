/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.L1_GibbsMeasure.PolymerRepresentation
import YangMills.L1_GibbsMeasure.SupportFactorization
import YangMills.ClayCore.GaugeMarginal
import YangMills.ClayCore.WilsonLoopMonomial
import YangMills.P8_PhysicalGap.SUN_StateConstruction
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

open MeasureTheory GaugeConfig

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

open Classical in
/-- **The ℝ↔ℂ bridge (V2 opening):** the far factors of the
loop-tagged expansion (ℂ-valued) are the CASTS of the real restricted
partition functions — so the `Z`-ratio bounds apply to them
verbatim. -/
theorem integral_prod_one_add_ofReal
    (μ : Measure G) [IsProbabilityMeasure μ]
    (w : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    (F : Finset (ConcretePlaquette d N)) :
    ∫ A, ∏ p ∈ F, ((1 : ℂ) + ((w A p : ℝ) : ℂ))
        ∂(gaugeMeasureFrom (d := d) (N := N) μ)
      = ((∫ A, ∏ p ∈ F, (1 + w A p)
          ∂(gaugeMeasureFrom (d := d) (N := N) μ) : ℝ) : ℂ) := by
  have hpt : (fun A : GaugeConfig d N G =>
      ∏ p ∈ F, ((1 : ℂ) + ((w A p : ℝ) : ℂ)))
      = fun A => (((∏ p ∈ F, (1 + w A p) : ℝ)) : ℂ) := by
    funext A
    push_cast
    rfl
  rw [hpt]
  exact integral_complex_ofReal

open Classical in
/-- **V2-1 — the neighbourhood-size count:** the far region's
complement is linear in the loop length and the pinned size, with
lattice-coordination constants only — every excluded plaquette either
meets the loop's support or touches a pinned plaquette. -/
theorem card_compl_farRegion_le (es : List (ConcreteEdge d N))
    (S₀ : Finset (ConcretePlaquette d N)) :
    (((farRegion es S₀)ᶜ).card : ℝ)
      ≤ (edgeSupport (d := d) (N := N) es).card * (4 * d)
        + S₀.card * (16 * d) := by
  classical
  have hsub : (farRegion es S₀)ᶜ
      ⊆ (edgeSupport (d := d) (N := N) es).biUnion
          (fun pe => (Finset.univ :
            Finset (ConcretePlaquette d N)).filter
            (fun q => pe ∈ plaquetteSupport q))
        ∪ S₀.biUnion (fun q => (Finset.univ :
            Finset (ConcretePlaquette d N)).filter
            (fun p => plaquetteTouches q p)) := by
    intro p hp
    rw [Finset.mem_compl, farRegion, Finset.mem_filter] at hp
    push_neg at hp
    rcases Classical.em (Disjoint (edgeSupport (d := d) (N := N) es)
        (plaquetteSupport p)) with hd | hd
    · obtain ⟨q, hqS, hqt⟩ := hp (Finset.mem_univ p) hd
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨q, hqS, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqt⟩⟩)
    · obtain ⟨pe, hpe1, hpe2⟩ := Finset.not_disjoint_iff.mp hd
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨pe, hpe1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpe2⟩⟩)
  calc (((farRegion es S₀)ᶜ).card : ℝ)
      ≤ ((((edgeSupport (d := d) (N := N) es).biUnion
          (fun pe => (Finset.univ :
            Finset (ConcretePlaquette d N)).filter
            (fun q => pe ∈ plaquetteSupport q))
        ∪ S₀.biUnion (fun q => (Finset.univ :
            Finset (ConcretePlaquette d N)).filter
            (fun p => plaquetteTouches q p))).card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ (((edgeSupport (d := d) (N := N) es).biUnion
          (fun pe => (Finset.univ :
            Finset (ConcretePlaquette d N)).filter
            (fun q => pe ∈ plaquetteSupport q))).card : ℝ)
        + ((S₀.biUnion (fun q => (Finset.univ :
            Finset (ConcretePlaquette d N)).filter
            (fun p => plaquetteTouches q p))).card : ℝ) := by
        exact_mod_cast Finset.card_union_le _ _
    _ ≤ (∑ pe ∈ edgeSupport (d := d) (N := N) es,
          (((Finset.univ : Finset (ConcretePlaquette d N)).filter
            (fun q => pe ∈ plaquetteSupport q)).card : ℝ))
        + ∑ q ∈ S₀,
          (((Finset.univ : Finset (ConcretePlaquette d N)).filter
            (fun p => plaquetteTouches q p)).card : ℝ) := by
        gcongr
        · exact_mod_cast Finset.card_biUnion_le
        · exact_mod_cast Finset.card_biUnion_le
    _ ≤ (∑ _pe ∈ edgeSupport (d := d) (N := N) es, ((4 * d : ℕ) : ℝ))
        + ∑ _q ∈ S₀, ((16 * d : ℕ) : ℝ) := by
        gcongr with pe _ q _
        · exact_mod_cast card_plaquettesThroughEdge_le pe
        · exact_mod_cast card_plaquettesTouching_le q
    _ = (edgeSupport (d := d) (N := N) es).card * (4 * d)
        + S₀.card * (16 * d) := by
        rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul,
          nsmul_eq_mul]
        push_cast
        ring

open Classical in
/-- Wilson lines are insensitive to configuration changes away from
their edges, at the CONFIG level (the `IsLocalWeight` interface). -/
theorem wilsonLine_congr_of_configToPos_eq
    {A A' : GaugeConfig d N G} (es : List (ConcreteEdge d N))
    (h : ∀ e ∈ es, configToPos A (ConcreteEdge.pos e)
      = configToPos A' (ConcreteEdge.pos e)) :
    wilsonLine A es = wilsonLine A' es := by
  induction es with
  | nil => rfl
  | cons e tl ih =>
      rw [wilsonLine_cons, wilsonLine_cons,
        config_eval_eq_of_pos A A' e (h e List.mem_cons_self),
        ih fun e' he' => h e' (List.mem_cons_of_mem _ he')]

open Classical in
/-- **The real linearized Wilson activity is a local weight (V2-3b′):**
`w_p(A) := 2·Re(c_p · tr H_p)` reads only the plaquette's support —
the form the restricted gate and the `Z`-ratio machinery consume. -/
theorem isLocalWeight_reActivity (N_c : ℕ) [NeZero N_c]
    (c : ConcretePlaquette d N → ℂ) :
    IsLocalWeight (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
      (fun A p => (2 : ℝ) * (c p * Matrix.trace (wilsonLine A
        (plaquetteList (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val).re) := by
  intro p A A' h
  have hW : wilsonLine A (plaquetteList (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)
      = wilsonLine A' (plaquetteList (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p) := by
    refine wilsonLine_congr_of_configToPos_eq _ fun e he => h _ ?_
    have hlist : e = p.edges 0 ∨ e = p.edges 1 ∨ e = p.edges 2
        ∨ e = p.edges 3 := by
      simpa [plaquetteList, List.mem_cons] using he
    rcases hlist with rfl | rfl | rfl | rfl <;>
      simp [plaquetteSupport, ConcreteEdge.pos]
  show (2 : ℝ) * (c p * Matrix.trace (wilsonLine A
      (plaquetteList (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val).re
    = (2 : ℝ) * (c p * Matrix.trace (wilsonLine A'
      (plaquetteList (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val).re
  rw [hW]

open Classical in
/-- The real linearized activity is measurable. -/
theorem measurable_reActivity (N_c : ℕ) [NeZero N_c]
    (c : ConcretePlaquette d N → ℂ) :
    ∀ p : ConcretePlaquette d N,
      Measurable (fun A : GaugeConfig d N
        (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) =>
        (2 : ℝ) * (c p * Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val).re) :=
  fun p => ((Complex.measurable_re.comp
    ((measurable_trace_wilsonLine _).const_mul (c p))).const_mul 2)

open Classical in
/-- The real linearized activity is uniformly bounded by `2δN_c`. -/
theorem reActivity_bound (N_c : ℕ) [NeZero N_c]
    {δ : ℝ} (c : ConcretePlaquette d N → ℂ) (hc : ∀ p, ‖c p‖ ≤ δ) :
    ∀ (A : GaugeConfig d N (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))
      (p : ConcretePlaquette d N),
      |(2 : ℝ) * (c p * Matrix.trace (wilsonLine A
        (plaquetteList (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val).re|
      ≤ 2 * δ * (N_c : ℝ) := by
  intro A p
  have hδ0 : (0 : ℝ) ≤ δ := le_trans (norm_nonneg (c p)) (hc p)
  rw [abs_mul, abs_two]
  have h1 := Complex.abs_re_le_norm (c p * Matrix.trace (wilsonLine A
    (plaquetteList (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)
  have h2 : ‖c p * Matrix.trace (wilsonLine A
      (plaquetteList (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val‖
      ≤ δ * (N_c : ℝ) := by
    rw [norm_mul]
    exact mul_le_mul (hc p) (norm_trace_wilsonLine_le A _)
      (norm_nonneg _) hδ0
  calc (2 : ℝ) * |(c p * Matrix.trace (wilsonLine A
      (plaquetteList (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val).re|
      ≤ 2 * (δ * (N_c : ℝ)) :=
        mul_le_mul_of_nonneg_left (le_trans h1 h2) (by norm_num)
    _ = 2 * δ * (N_c : ℝ) := by ring

open Classical in
/-- **The conjugate-pair activity is the cast of the real one:** at
`c' = conj c`, the ℂ-activity factor of the loop-tagged expansion is
the cast of `1 + w_p` — connecting V2-3a's complex form with the
restricted gate's real form. -/
theorem one_add_conjPair_eq_cast (N_c : ℕ) [NeZero N_c]
    (c : ConcretePlaquette d N → ℂ)
    (A : GaugeConfig d N (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))
    (p : ConcretePlaquette d N) :
    (1 : ℂ) + (c p * Matrix.trace (wilsonLine A
        (plaquetteList (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
      + (starRingEnd ℂ) (c p) * star (Matrix.trace (wilsonLine A
        (plaquetteList (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val))
      = ((1 + (2 : ℝ) * (c p * Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val).re
          : ℝ) : ℂ) := by
  have hpair : c p * Matrix.trace (wilsonLine A
      (plaquetteList (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
      + (starRingEnd ℂ) (c p) * star (Matrix.trace (wilsonLine A
        (plaquetteList (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)
      = (c p * Matrix.trace (wilsonLine A
        (plaquetteList (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)
      + (starRingEnd ℂ) (c p * Matrix.trace (wilsonLine A
        (plaquetteList (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val) := by
    rw [map_mul]
    rfl
  rw [hpair, Complex.add_conj]
  push_cast
  ring

open Classical in
/-- **The far factor at the conjugate pair is the cast of the real
restricted `Z` (V2-3b′ identification):** the ℂ-valued far factors of
the loop-tagged expansion ARE the real restricted partition functions
the gate machinery controls. -/
theorem integral_conjPair_prod_eq_cast (N_c : ℕ) [NeZero N_c]
    (μ : Measure (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))
    [IsProbabilityMeasure μ]
    (c : ConcretePlaquette d N → ℂ)
    (F : Finset (ConcretePlaquette d N)) :
    ∫ A, ∏ p ∈ F, ((1 : ℂ)
        + (c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + (starRingEnd ℂ) (c p) * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)))
        ∂(gaugeMeasureFrom (d := d) (N := N) μ)
      = ((∫ A, ∏ p ∈ F, (1 + (2 : ℝ) * (c p * Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val).re)
          ∂(gaugeMeasureFrom (d := d) (N := N) μ) : ℝ) : ℂ) := by
  have hpt : (fun A : GaugeConfig d N
      (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) =>
      ∏ p ∈ F, ((1 : ℂ)
        + (c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + (starRingEnd ℂ) (c p) * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val))))
      = fun A => ∏ p ∈ F, ((1 : ℂ)
          + (((2 : ℝ) * (c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val).re
            : ℝ) : ℂ)) := by
    funext A
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [one_add_conjPair_eq_cast N_c c A p]
    push_cast
    ring
  rw [hpt]
  exact integral_prod_one_add_ofReal μ _ F

set_option maxHeartbeats 1600000 in
open Classical in
/-- **V2-3b′ — THE NORMALIZED PINNED BOUND** (the `Z`-ratio
cancellation executed): at strong coupling, the NORMALIZED Wilson-loop
expectation is bounded by the pinned sum of dichotomy weights times
loop-neighbourhood exponentials — every factor volume-free. -/
theorem norm_normalized_wilson_loop_le_pinned_sum
    (N_c : ℕ) [NeZero N_c]
    (es : List (ConcreteEdge d N)) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (c c' : ConcretePlaquette d N → ℂ)
    (hc : ∀ p, ‖c p‖ ≤ δ) (hc' : ∀ p, ‖c' p‖ ≤ δ)
    (hpair : ∀ p, c' p = (starRingEnd ℂ) (c p))
    (t ε : ℝ) (ht0 : 0 ≤ t) (hε0 : 0 ≤ ε)
    (hr : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      ((2 * δ * (N_c : ℝ)) * Real.exp (t + ε + 1)) < 1)
    (hsmall : ((16 * d : ℕ) : ℝ) *
      (((2 * δ * (N_c : ℝ)) * Real.exp (t + ε + 1)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          ((2 * δ * (N_c : ℝ)) * Real.exp (t + ε + 1)))) ≤ t)
    (hint1 : ∀ S : Finset (ConcretePlaquette d N),
      Integrable (fun A => Matrix.trace (wilsonLine A es).val *
        ∏ p ∈ S, (c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + c' p * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)))
        (gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)))
    (hint2 : ∀ S : Finset (ConcretePlaquette d N),
      Integrable (fun A => ∏ p ∈ S,
        (c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + c' p * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)))
        (gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c))) :
    ‖(∫ A, Matrix.trace (wilsonLine A es).val *
        ∏ p : ConcretePlaquette d N,
          (1 + (c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + c' p * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)))
        ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)))
      / ((weightedPartition (d := d) (N := N) (sunHaarProb N_c)
          (fun A p => (2 : ℝ) * (c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val).re)
          : ℝ) : ℂ)‖
      ≤ ∑ S₀ ∈ (Finset.univ :
            Finset (ConcretePlaquette d N)).powerset.filter
            (fun S₀ => nearLoop es S₀ = S₀),
          (if chainAreaA (R := ZMod N_c) (d := d) (N := N)
                (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
                (loopChain (R := ZMod N_c) (d := d) (N := N)
                  (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) es)
              ≤ S₀.card
            then (N_c : ℝ) * (2 * δ * (N_c : ℝ)) ^ S₀.card
            else 0) *
          Real.exp
            (((edgeSupport (d := d) (N := N) es).card * (4 * d)
              + S₀.card * (16 * d)) *
              (Real.exp 1 * ((2 * δ * (N_c : ℝ) * Real.exp t) /
                (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
                  (2 * δ * (N_c : ℝ) * Real.exp t))))) := by
  classical
  set w : GaugeConfig d N (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
      → ConcretePlaquette d N → ℝ :=
    fun A p => (2 : ℝ) * (c p * Matrix.trace (wilsonLine A
      (plaquetteList (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val).re
    with hw
  have hloc := isLocalWeight_reActivity (d := d) (N := N) N_c c
  have hmeas := measurable_reActivity (d := d) (N := N) N_c c
  have hbd := reActivity_bound (d := d) (N := N) N_c c hc
  have hδw0 : (0 : ℝ) ≤ 2 * δ * (N_c : ℝ) := by positivity
  have hx0 : (0 : ℝ) ≤ 2 * δ * (N_c : ℝ) * Real.exp t := by positivity
  have hr' : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      (2 * δ * (N_c : ℝ) * Real.exp t) < 1 := by
    refine lt_of_le_of_lt ?_ hr
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine mul_le_mul_of_nonneg_left ?_ hδw0
    exact Real.exp_le_exp.mpr (by linarith)
  have hK0 : (0 : ℝ) ≤ Real.exp 1 *
      ((2 * δ * (N_c : ℝ) * Real.exp t) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          (2 * δ * (N_c : ℝ) * Real.exp t))) := by
    have hden : (0 : ℝ) < 1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
        (2 * δ * (N_c : ℝ) * Real.exp t) := by linarith
    positivity
  -- the gate, per region
  have hgate := fun S₀ : Finset (ConcretePlaquette d N) =>
    restricted_partition_log_ratio_bound (sunHaarProb N_c)
      hloc hmeas hδw0 hbd t ε ht0 hε0 hr hsmall (farRegion es S₀)
  -- the base criterion and Z = exp ζ
  have hscale1 := weighted_scale_kpCriterion (sunHaarProb N_c)
    hδw0 hbd t ε 1 ht0 hε0 (by linarith) hr hsmall
  have hcrit : KP.KPCriterion
      (weightedLatticePolymerSystem (d := d) (N := N)
        (sunHaarProb N_c) w)
      (fun cc => t * (cc.1.card : ℝ)) := by
    refine KP.KPCriterion.of_activity_norm_le
      (z₂ := fun cc : (weightedLatticePolymerSystem (d := d) (N := N)
          (sunHaarProb N_c) w).Polymer =>
        ((Real.exp 1 : ℝ) : ℂ) *
          (weightedLatticePolymerSystem (d := d) (N := N)
            (sunHaarProb N_c) w).activity cc)
      ?_ hscale1
    intro cc
    rw [norm_mul]
    refine le_mul_of_one_le_left (norm_nonneg _) ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.one_le_exp (zero_le_one (α := ℝ))
  have hZ : ((weightedPartition (d := d) (N := N) (sunHaarProb N_c) w
      : ℝ) : ℂ)
      = Complex.exp (KP.clusterSum
        (weightedLatticePolymerSystem (d := d) (N := N)
          (sunHaarProb N_c) w)) := by
    rw [weightedPartition_eq_partition (sunHaarProb N_c) hloc hmeas hbd]
    exact KP.partition_eq_exp_clusterSum_of_kp _ hcrit
  -- the numerator bound with exp-identified far factors
  have h3a := norm_integral_wilson_loop_le_pinned_sum es δ hδ0 c c'
    hc hc' hint1 hint2
  simp only [hpair] at h3a
  have hnum : ‖∫ A, Matrix.trace (wilsonLine A es).val *
      ∏ p : ConcretePlaquette d N,
        (1 + (c p * Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
        + (starRingEnd ℂ) (c p) * star (Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)))
      ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c))‖
      ≤ ∑ S₀ ∈ (Finset.univ :
          Finset (ConcretePlaquette d N)).powerset.filter
          (fun S₀ => nearLoop es S₀ = S₀),
        (if chainAreaA (R := ZMod N_c) (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
              (loopChain (R := ZMod N_c) (d := d) (N := N)
                (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) es)
            ≤ S₀.card
          then (N_c : ℝ) * (2 * δ * (N_c : ℝ)) ^ S₀.card
          else 0) *
        ‖Complex.exp (KP.clusterSum
          ((weightedLatticePolymerSystem (d := d) (N := N)
            (sunHaarProb N_c) w).restrict
            (Finset.univ.filter
              (fun cc => cc.1 ⊆ farRegion es S₀))))‖ := by
    refine le_trans h3a (le_of_eq (Finset.sum_congr rfl fun S₀ _ => ?_))
    have hfar := (integral_conjPair_prod_eq_cast N_c (sunHaarProb N_c) c
      (farRegion es S₀)).trans (hgate S₀).1
    rw [hfar]
  -- the difference bounds, per region
  have hdiff : ∀ S₀ ∈ (Finset.univ :
      Finset (ConcretePlaquette d N)).powerset.filter
      (fun S₀ => nearLoop es S₀ = S₀),
      ‖KP.clusterSum (weightedLatticePolymerSystem (d := d) (N := N)
          (sunHaarProb N_c) w)
        - KP.clusterSum ((weightedLatticePolymerSystem (d := d) (N := N)
          (sunHaarProb N_c) w).restrict
          (Finset.univ.filter (fun cc => cc.1 ⊆ farRegion es S₀)))‖
      ≤ ((edgeSupport (d := d) (N := N) es).card * (4 * d)
          + S₀.card * (16 * d)) *
        (Real.exp 1 * ((2 * δ * (N_c : ℝ) * Real.exp t) /
          (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
            (2 * δ * (N_c : ℝ) * Real.exp t)))) := by
    intro S₀ _
    refine le_trans (hgate S₀).2 ?_
    refine le_trans (offRegion_polymer_sum_le (sunHaarProb N_c)
      hδw0 hbd t ht0 hr' (farRegion es S₀)) ?_
    exact mul_le_mul_of_nonneg_right
      (card_compl_farRegion_le es S₀) hK0
  -- assemble
  refine KP.norm_div_le_pinned_sum_exp _ _ _ _ _ _ _
    (fun S₀ _ => ?_) ?_ hZ hdiff
  · split_ifs
    · positivity
    · exact le_rfl
  · have hNumEq : (∫ A, Matrix.trace (wilsonLine A es).val *
        ∏ p : ConcretePlaquette d N,
          (1 + (c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + c' p * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)))
        ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)))
        = ∫ A, Matrix.trace (wilsonLine A es).val *
        ∏ p : ConcretePlaquette d N,
          (1 + (c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + (starRingEnd ℂ) (c p) * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)))
        ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun A => ?_)
      refine congrArg (fun x => Matrix.trace (wilsonLine A es).val * x) ?_
      exact Finset.prod_congr rfl fun p _ => by rw [hpair p]
    rw [hNumEq]
    exact hnum

open Classical in
/-- **The loop-touching polymer sum (V2-3c entropy):** the σ-weighted
sum over connected polymers touching the loop's edge support is at most
the loop-neighbourhood count `#loopSupp·4d` times the volume-free
per-plaquette geometric sum — every touching polymer is charged to a
loop-adjacent plaquette it contains. -/
theorem loopTouching_polymer_sum_le (es : List (ConcreteEdge d N))
    (σ : ℝ) (h0 : 0 ≤ σ)
    (hr : ((16 * d + 1 : ℕ) : ℝ) ^ 2 * σ < 1) :
    (∑ c ∈ (Finset.univ :
        Finset (Finset (ConcretePlaquette d N))).filter
        (fun c => (c.Nonempty ∧ IsConnectedPolymer c) ∧
          ∃ p ∈ c, ¬ Disjoint (edgeSupport (d := d) (N := N) es)
            (plaquetteSupport p)),
      σ ^ c.card)
    ≤ ((edgeSupport (d := d) (N := N) es).card : ℝ) * (4 * (d : ℝ)) *
        (σ / (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 * σ)) := by
  classical
  set L : Finset (ConcretePlaquette d N) := Finset.univ.filter
    (fun p => ¬ Disjoint (edgeSupport (d := d) (N := N) es)
      (plaquetteSupport p)) with hLdef
  have hden : (0 : ℝ) < 1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 * σ := by linarith
  have hconst0 : (0 : ℝ) ≤ σ / (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 * σ) :=
    div_nonneg h0 hden.le
  -- the per-plaquette injection into the subtype filter
  have hsub_p : ∀ p : ConcretePlaquette d N,
      ((Finset.univ :
        Finset (Finset (ConcretePlaquette d N))).filter
        (fun c => (c.Nonempty ∧ IsConnectedPolymer c) ∧
          ∃ q ∈ c, ¬ Disjoint (edgeSupport (d := d) (N := N) es)
            (plaquetteSupport q))).filter (fun c => p ∈ c)
      ⊆ ((Finset.univ : Finset {c : Finset (ConcretePlaquette d N) //
          c.Nonempty ∧ IsConnectedPolymer c}).filter
          (fun c' => p ∈ c'.1)).image (fun c' => c'.1) := by
    intro p c hc
    have hc1 := Finset.mem_filter.mp hc
    have hc2 := Finset.mem_filter.mp hc1.1
    refine Finset.mem_image.mpr ⟨⟨c, hc2.2.1⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc1.2⟩
  have himg : ∀ p : ConcretePlaquette d N,
      (∑ T ∈ ((Finset.univ :
          Finset {c : Finset (ConcretePlaquette d N) //
            c.Nonempty ∧ IsConnectedPolymer c}).filter
          (fun c' => p ∈ c'.1)).image (fun c' => c'.1),
        σ ^ T.card)
      = ∑ c' ∈ (Finset.univ :
          Finset {c : Finset (ConcretePlaquette d N) //
            c.Nonempty ∧ IsConnectedPolymer c}).filter
          (fun c' => p ∈ c'.1),
        σ ^ c'.1.card :=
    fun p => Finset.sum_image
      (f := fun T : Finset (ConcretePlaquette d N) => σ ^ T.card)
      (g := fun c' : {c : Finset (ConcretePlaquette d N) //
        c.Nonempty ∧ IsConnectedPolymer c} => c'.1)
      (fun a _ b _ h => Subtype.ext h)
  calc (∑ c ∈ (Finset.univ :
        Finset (Finset (ConcretePlaquette d N))).filter
        (fun c => (c.Nonempty ∧ IsConnectedPolymer c) ∧
          ∃ p ∈ c, ¬ Disjoint (edgeSupport (d := d) (N := N) es)
            (plaquetteSupport p)),
      σ ^ c.card)
      ≤ ∑ c ∈ (Finset.univ :
          Finset (Finset (ConcretePlaquette d N))).filter
          (fun c => (c.Nonempty ∧ IsConnectedPolymer c) ∧
            ∃ p ∈ c, ¬ Disjoint (edgeSupport (d := d) (N := N) es)
              (plaquetteSupport p)),
          ∑ p ∈ L, (if p ∈ c then σ ^ c.card else 0) := by
        refine Finset.sum_le_sum fun c hc => ?_
        obtain ⟨-, -, p, hpc, hptouch⟩ := Finset.mem_filter.mp hc
        have hpL : p ∈ L := by
          rw [hLdef]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hptouch⟩
        have hkey : σ ^ c.card ≤ if p ∈ c then σ ^ c.card else 0 := by
          rw [if_pos hpc]
        refine le_trans hkey ?_
        refine Finset.single_le_sum
          (f := fun q => if q ∈ c then σ ^ c.card else 0)
          (fun q _ => ?_) hpL
        show (0 : ℝ) ≤ if q ∈ c then σ ^ c.card else 0
        split_ifs
        · exact pow_nonneg h0 _
        · exact le_rfl
    _ = ∑ p ∈ L, ∑ c ∈ (Finset.univ :
          Finset (Finset (ConcretePlaquette d N))).filter
          (fun c => (c.Nonempty ∧ IsConnectedPolymer c) ∧
            ∃ q ∈ c, ¬ Disjoint (edgeSupport (d := d) (N := N) es)
              (plaquetteSupport q)),
          (if p ∈ c then σ ^ c.card else 0) :=
        Finset.sum_comm
    _ ≤ ∑ _p ∈ L, σ / (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 * σ) := by
        refine Finset.sum_le_sum fun p _ => ?_
        rw [← Finset.sum_filter]
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (hsub_p p)
          (fun c _ _ => pow_nonneg h0 _)) ?_
        rw [himg p]
        exact sum_connectedPolymers_through_le (d := d) (N := N) p σ h0 hr
    _ = (L.card : ℝ) * (σ / (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 * σ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((edgeSupport (d := d) (N := N) es).card : ℝ) * (4 * (d : ℝ)) *
          (σ / (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 * σ)) := by
        refine mul_le_mul_of_nonneg_right ?_ hconst0
        have hLeq : L
            = (farRegion es (∅ : Finset (ConcretePlaquette d N)))ᶜ := by
          rw [hLdef]
          ext p
          rw [Finset.mem_filter, Finset.mem_compl, farRegion,
            Finset.mem_filter]
          constructor
          · rintro ⟨-, h⟩ hcon
            exact h hcon.2.1
          · intro h
            refine ⟨Finset.mem_univ _, fun hd => ?_⟩
            exact h ⟨Finset.mem_univ _, hd,
              fun q hq => absurd hq (Finset.notMem_empty q)⟩
        rw [hLeq]
        have hcompl := card_compl_farRegion_le (d := d) (N := N) es
          (∅ : Finset (ConcretePlaquette d N))
        simpa using hcompl

open Classical in
/-- **THE PINNED GAS TAIL (V2-3c closed):** the σ-weighted sum over
pinned sets is bounded by a PERIMETER exponential — volume-free in
every factor.  Chains the pinned resummation
(`sum_pinned_pow_le_prod`), the elementary gas exponentiation
(`prod_one_add_le_exp_sum`), and the loop-touching entropy bound. -/
theorem sum_pinned_pow_le_exp (es : List (ConcreteEdge d N))
    (σ : ℝ) (h0 : 0 ≤ σ)
    (hr : ((16 * d + 1 : ℕ) : ℝ) ^ 2 * σ < 1) :
    (∑ S₀ ∈ (Finset.univ :
        Finset (ConcretePlaquette d N)).powerset.filter
        (fun S₀ => nearLoop es S₀ = S₀),
      σ ^ S₀.card)
    ≤ Real.exp (((edgeSupport (d := d) (N := N) es).card : ℝ)
        * (4 * (d : ℝ))
        * (σ / (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 * σ))) := by
  refine le_trans (sum_pinned_pow_le_prod es σ h0) ?_
  refine le_trans (prod_one_add_le_exp_sum _ _
    (fun c _ => pow_nonneg h0 _)) ?_
  exact Real.exp_le_exp.mpr (loopTouching_polymer_sum_le es σ h0 hr)

open Classical in
/-- **The pinned dichotomy collapse (V2-3c arithmetic):** the pinned
sum of dichotomy weights times size-linear exponentials collapses to
`area weight × perimeter exponential` — abstract constants, ready for
the 3b′ instantiation. -/
theorem sum_pinned_dichotomy_le (es : List (ConcreteEdge d N)) (A : ℕ)
    (Cn K₁ K₂ ρ₀ σ : ℝ) (hCn : 0 ≤ Cn) (hρ₀ : 0 ≤ ρ₀)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hrσ : ((16 * d + 1 : ℕ) : ℝ) ^ 2 * σ < 1)
    (hρσ : ρ₀ * Real.exp K₂ ≤ σ ^ 2) :
    (∑ S₀ ∈ (Finset.univ :
        Finset (ConcretePlaquette d N)).powerset.filter
        (fun S₀ => nearLoop es S₀ = S₀),
      (if A ≤ S₀.card then Cn * ρ₀ ^ S₀.card else 0) *
        Real.exp (K₁ + (S₀.card : ℝ) * K₂))
    ≤ Cn * Real.exp K₁ * σ ^ A *
        Real.exp (((edgeSupport (d := d) (N := N) es).card : ℝ)
          * (4 * (d : ℝ))
          * (σ / (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 * σ))) := by
  classical
  have hCnK : (0 : ℝ) ≤ Cn * Real.exp K₁ :=
    mul_nonneg hCn (Real.exp_pos _).le
  have hterm : ∀ S₀ : Finset (ConcretePlaquette d N),
      (if A ≤ S₀.card then Cn * ρ₀ ^ S₀.card else 0) *
        Real.exp (K₁ + (S₀.card : ℝ) * K₂)
      ≤ Cn * Real.exp K₁ *
          (if A ≤ S₀.card then (σ ^ 2) ^ S₀.card else 0) := by
    intro S₀
    split_ifs with h
    · have hexp : Real.exp (K₁ + (S₀.card : ℝ) * K₂)
          = Real.exp K₁ * Real.exp K₂ ^ S₀.card := by
        rw [Real.exp_add, Real.exp_nat_mul]
      calc (Cn * ρ₀ ^ S₀.card) * Real.exp (K₁ + (S₀.card : ℝ) * K₂)
          = Cn * Real.exp K₁ * (ρ₀ * Real.exp K₂) ^ S₀.card := by
            rw [hexp, mul_pow]
            ring
        _ ≤ Cn * Real.exp K₁ * (σ ^ 2) ^ S₀.card := by
            refine mul_le_mul_of_nonneg_left ?_ hCnK
            exact pow_le_pow_left₀
              (mul_nonneg hρ₀ (Real.exp_pos _).le) hρσ _
    · rw [zero_mul, mul_zero]
  calc (∑ S₀ ∈ (Finset.univ :
        Finset (ConcretePlaquette d N)).powerset.filter
        (fun S₀ => nearLoop es S₀ = S₀),
      (if A ≤ S₀.card then Cn * ρ₀ ^ S₀.card else 0) *
        Real.exp (K₁ + (S₀.card : ℝ) * K₂))
      ≤ ∑ S₀ ∈ (Finset.univ :
          Finset (ConcretePlaquette d N)).powerset.filter
          (fun S₀ => nearLoop es S₀ = S₀),
          Cn * Real.exp K₁ *
            (if A ≤ S₀.card then (σ ^ 2) ^ S₀.card else 0) :=
        Finset.sum_le_sum fun S₀ _ => hterm S₀
    _ = Cn * Real.exp K₁ * ∑ S₀ ∈ (Finset.univ :
          Finset (ConcretePlaquette d N)).powerset.filter
          (fun S₀ => nearLoop es S₀ = S₀),
          (if A ≤ S₀.card then (σ ^ 2) ^ S₀.card else 0) := by
        rw [Finset.mul_sum]
    _ ≤ Cn * Real.exp K₁ * (σ ^ A * ∑ S₀ ∈ (Finset.univ :
          Finset (ConcretePlaquette d N)).powerset.filter
          (fun S₀ => nearLoop es S₀ = S₀),
          σ ^ S₀.card) := by
        refine mul_le_mul_of_nonneg_left ?_ hCnK
        exact KP.sum_ite_pow_le _ Finset.card A σ hσ0 hσ1
    _ ≤ Cn * Real.exp K₁ * (σ ^ A *
          Real.exp (((edgeSupport (d := d) (N := N) es).card : ℝ)
            * (4 * (d : ℝ))
            * (σ / (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 * σ)))) := by
        refine mul_le_mul_of_nonneg_left ?_ hCnK
        exact mul_le_mul_of_nonneg_left
          (sum_pinned_pow_le_exp es σ hσ0 hrσ) (pow_nonneg hσ0 _)
    _ = Cn * Real.exp K₁ * σ ^ A *
          Real.exp (((edgeSupport (d := d) (N := N) es).card : ℝ)
            * (4 * (d : ℝ))
            * (σ / (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 * σ))) := by
        ring

set_option maxHeartbeats 1600000 in
open Classical in
/-- **THE VOLUME-UNIFORM AREA LAW — the VU campaign headline.**

At strong coupling (conjugate-pair linearized activities, `‖c‖ ≤ δ`,
in the banked smallness window), for ANY area-extraction rate
`σ ∈ [0,1)` with `2δN_c·e^{16d·K} ≤ σ²`:

`‖⟨tr W_C⟩‖ ≤ N_c · e^{#loopSupp·4d·K} · σ^{Area(C)} · e^{#loopSupp·4d·S(σ)}`

— the area-law decay `σ^{Area}` with a PERIMETER-ONLY prefactor:
every constant is volume-free, the bound holds on every finite
lattice uniformly.  `Z` cancelled through the restricted cluster
expansion; the pinned gas resummed by elementary entropy. -/
theorem normalized_wilson_loop_area_law
    (N_c : ℕ) [NeZero N_c]
    (es : List (ConcreteEdge d N)) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (c c' : ConcretePlaquette d N → ℂ)
    (hc : ∀ p, ‖c p‖ ≤ δ) (hc' : ∀ p, ‖c' p‖ ≤ δ)
    (hpair : ∀ p, c' p = (starRingEnd ℂ) (c p))
    (t ε : ℝ) (ht0 : 0 ≤ t) (hε0 : 0 ≤ ε)
    (hr : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      ((2 * δ * (N_c : ℝ)) * Real.exp (t + ε + 1)) < 1)
    (hsmall : ((16 * d : ℕ) : ℝ) *
      (((2 * δ * (N_c : ℝ)) * Real.exp (t + ε + 1)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          ((2 * δ * (N_c : ℝ)) * Real.exp (t + ε + 1)))) ≤ t)
    (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hrσ : ((16 * d + 1 : ℕ) : ℝ) ^ 2 * σ < 1)
    (hρσ : (2 * δ * (N_c : ℝ)) *
        Real.exp ((16 * (d : ℝ)) *
          (Real.exp 1 * ((2 * δ * (N_c : ℝ) * Real.exp t) /
            (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
              (2 * δ * (N_c : ℝ) * Real.exp t)))))
        ≤ σ ^ 2)
    (hint1 : ∀ S : Finset (ConcretePlaquette d N),
      Integrable (fun A => Matrix.trace (wilsonLine A es).val *
        ∏ p ∈ S, (c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + c' p * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)))
        (gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)))
    (hint2 : ∀ S : Finset (ConcretePlaquette d N),
      Integrable (fun A => ∏ p ∈ S,
        (c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + c' p * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)))
        (gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c))) :
    ‖(∫ A, Matrix.trace (wilsonLine A es).val *
        ∏ p : ConcretePlaquette d N,
          (1 + (c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + c' p * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)))
        ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)))
      / ((weightedPartition (d := d) (N := N) (sunHaarProb N_c)
          (fun A p => (2 : ℝ) * (c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val).re)
          : ℝ) : ℂ)‖
      ≤ (N_c : ℝ) *
          Real.exp (((edgeSupport (d := d) (N := N) es).card : ℝ)
            * (4 * (d : ℝ))
            * (Real.exp 1 * ((2 * δ * (N_c : ℝ) * Real.exp t) /
              (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
                (2 * δ * (N_c : ℝ) * Real.exp t))))) *
          σ ^ (chainAreaA (R := ZMod N_c) (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
            (loopChain (R := ZMod N_c) (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) es)) *
          Real.exp (((edgeSupport (d := d) (N := N) es).card : ℝ)
            * (4 * (d : ℝ))
            * (σ / (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 * σ))) := by
  classical
  refine le_trans (norm_normalized_wilson_loop_le_pinned_sum N_c es δ hδ0
    c c' hc hc' hpair t ε ht0 hε0 hr hsmall hint1 hint2) ?_
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun S₀ _ => ?_))
    (sum_pinned_dichotomy_le es
      (chainAreaA (R := ZMod N_c) (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
        (loopChain (R := ZMod N_c) (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) es))
      ((N_c : ℝ))
      (((edgeSupport (d := d) (N := N) es).card : ℝ) * (4 * (d : ℝ))
        * (Real.exp 1 * ((2 * δ * (N_c : ℝ) * Real.exp t) /
          (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
            (2 * δ * (N_c : ℝ) * Real.exp t)))))
      ((16 * (d : ℝ))
        * (Real.exp 1 * ((2 * δ * (N_c : ℝ) * Real.exp t) /
          (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
            (2 * δ * (N_c : ℝ) * Real.exp t)))))
      (2 * δ * (N_c : ℝ)) σ
      (Nat.cast_nonneg _)
      (mul_nonneg (mul_nonneg (by norm_num) hδ0) (Nat.cast_nonneg _))
      hσ0 hσ1 hrσ hρσ)
  congr 1
  exact congrArg Real.exp (by ring)

open Classical in
/-- **Integrability discharge (i):** the conjugate-pair product
integrands are integrable — measurable (decorated expansion) and
bounded (finite product of trace bounds).  No smallness needed. -/
theorem integrable_conjPair_prod (N_c : ℕ) [NeZero N_c]
    (c c' : ConcretePlaquette d N → ℂ)
    (S : Finset (ConcretePlaquette d N)) :
    Integrable (fun A => ∏ p ∈ S,
      (c p * Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
        + c' p * star (Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)))
      (gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)) := by
  classical
  have hm : Measurable (fun A : GaugeConfig d N
      (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) => ∏ p ∈ S,
      (c p * Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
        + c' p * star (Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val))) :=
    Finset.measurable_prod _ fun p _ =>
      ((measurable_const.mul (measurable_trace_wilsonLine _)).add
        (measurable_const.mul (continuous_star.measurable.comp
          (measurable_trace_wilsonLine _))))
  have hb : ∀ A : GaugeConfig d N
      (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)),
      ‖∏ p ∈ S,
        (c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + c' p * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val))‖
        ≤ ∏ p ∈ S, (‖c p‖ * (N_c : ℝ) + ‖c' p‖ * (N_c : ℝ)) := by
    intro A
    rw [norm_prod]
    refine Finset.prod_le_prod (fun p _ => norm_nonneg _) (fun p _ => ?_)
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, norm_mul, norm_star]
    exact add_le_add
      (mul_le_mul_of_nonneg_left
        (norm_trace_wilsonLine_le A _) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left
        (norm_trace_wilsonLine_le A _) (norm_nonneg _))
  have h2 := (integrable_const (1 : ℂ)
    (μ := gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c))).bdd_mul
    hm.aestronglyMeasurable (MeasureTheory.ae_of_all _ hb)
  simpa using h2

open Classical in
/-- **Integrability discharge (ii):** the trace-times-product
integrands are integrable — measurable and bounded.  No smallness
needed. -/
theorem integrable_trace_mul_conjPair_prod (N_c : ℕ) [NeZero N_c]
    (es : List (ConcreteEdge d N))
    (c c' : ConcretePlaquette d N → ℂ)
    (S : Finset (ConcretePlaquette d N)) :
    Integrable (fun A => Matrix.trace (wilsonLine A es).val * ∏ p ∈ S,
      (c p * Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
        + c' p * star (Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)))
      (gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)) := by
  classical
  have hm : Measurable (fun A : GaugeConfig d N
      (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) =>
      Matrix.trace (wilsonLine A es).val * ∏ p ∈ S,
      (c p * Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
        + c' p * star (Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val))) :=
    (measurable_trace_wilsonLine es).mul
      (Finset.measurable_prod _ fun p _ =>
        ((measurable_const.mul (measurable_trace_wilsonLine _)).add
          (measurable_const.mul (continuous_star.measurable.comp
          (measurable_trace_wilsonLine _)))))
  have hb : ∀ A : GaugeConfig d N
      (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)),
      ‖Matrix.trace (wilsonLine A es).val * ∏ p ∈ S,
        (c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + c' p * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val))‖
        ≤ (N_c : ℝ) *
            ∏ p ∈ S, (‖c p‖ * (N_c : ℝ) + ‖c' p‖ * (N_c : ℝ)) := by
    intro A
    rw [norm_mul]
    refine mul_le_mul (norm_trace_wilsonLine_le A es) ?_
      (norm_nonneg _) (Nat.cast_nonneg _)
    rw [norm_prod]
    refine Finset.prod_le_prod (fun p _ => norm_nonneg _) (fun p _ => ?_)
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, norm_mul, norm_star]
    exact add_le_add
      (mul_le_mul_of_nonneg_left
        (norm_trace_wilsonLine_le A _) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left
        (norm_trace_wilsonLine_le A _) (norm_nonneg _))
  have h2 := (integrable_const (1 : ℂ)
    (μ := gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c))).bdd_mul
    hm.aestronglyMeasurable (MeasureTheory.ae_of_all _ hb)
  simpa using h2

set_option maxHeartbeats 1600000 in
open Classical in
/-- **THE VOLUME-UNIFORM AREA LAW, UNCONDITIONAL ON THE LATTICE SIDE:**
the headline with both integrability families DISCHARGED — every
hypothesis is now an explicit smallness/geometry condition. -/
theorem normalized_wilson_loop_area_law_unconditional
    (N_c : ℕ) [NeZero N_c]
    (es : List (ConcreteEdge d N)) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (c c' : ConcretePlaquette d N → ℂ)
    (hc : ∀ p, ‖c p‖ ≤ δ) (hc' : ∀ p, ‖c' p‖ ≤ δ)
    (hpair : ∀ p, c' p = (starRingEnd ℂ) (c p))
    (t ε : ℝ) (ht0 : 0 ≤ t) (hε0 : 0 ≤ ε)
    (hr : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      ((2 * δ * (N_c : ℝ)) * Real.exp (t + ε + 1)) < 1)
    (hsmall : ((16 * d : ℕ) : ℝ) *
      (((2 * δ * (N_c : ℝ)) * Real.exp (t + ε + 1)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          ((2 * δ * (N_c : ℝ)) * Real.exp (t + ε + 1)))) ≤ t)
    (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hrσ : ((16 * d + 1 : ℕ) : ℝ) ^ 2 * σ < 1)
    (hρσ : (2 * δ * (N_c : ℝ)) *
        Real.exp ((16 * (d : ℝ)) *
          (Real.exp 1 * ((2 * δ * (N_c : ℝ) * Real.exp t) /
            (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
              (2 * δ * (N_c : ℝ) * Real.exp t)))))
        ≤ σ ^ 2) :
    ‖(∫ A, Matrix.trace (wilsonLine A es).val *
        ∏ p : ConcretePlaquette d N,
          (1 + (c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + c' p * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)))
        ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)))
      / ((weightedPartition (d := d) (N := N) (sunHaarProb N_c)
          (fun A p => (2 : ℝ) * (c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val).re)
          : ℝ) : ℂ)‖
      ≤ (N_c : ℝ) *
          Real.exp (((edgeSupport (d := d) (N := N) es).card : ℝ)
            * (4 * (d : ℝ))
            * (Real.exp 1 * ((2 * δ * (N_c : ℝ) * Real.exp t) /
              (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
                (2 * δ * (N_c : ℝ) * Real.exp t))))) *
          σ ^ (chainAreaA (R := ZMod N_c) (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
            (loopChain (R := ZMod N_c) (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) es)) *
          Real.exp (((edgeSupport (d := d) (N := N) es).card : ℝ)
            * (4 * (d : ℝ))
            * (σ / (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 * σ))) :=
  normalized_wilson_loop_area_law N_c es δ hδ0 c c' hc hc' hpair
    t ε ht0 hε0 hr hsmall σ hσ0 hσ1 hrσ hρσ
    (fun S => integrable_trace_mul_conjPair_prod N_c es c c' S)
    (fun S => integrable_conjPair_prod N_c c c' S)

/-! ## V4 opening: the exact Wilson factor `∏ exp(z_p)`

`docs/AREA-LAW-VU-PLAN.md` V4.  At the conjugate pair `c' = conj c`
the Wilson Boltzmann exponent is REAL,
`z_p(A) = 2·Re(c_p · tr H_p)`, so the exact factor
`exp(z_p) = 1 + (exp(z_p) − 1)` is the linearized form with the REAL,
bounded, local activity `expReActivity := exp(2 Re(c·tr H)) − 1`.  The
generic VU pipeline (loop-tagged expansion + restricted `Z`
cancellation) consumes exactly the interface below; only the per-pinned
dichotomy must be re-derived (the exp version of the N-ality kill,
V4-1). -/

/-- The **exact (exponential) Wilson activity** at the conjugate pair:
`exp(z_p) − 1` with the real exponent `z_p = 2·Re(c_p · tr H_p)`. -/
noncomputable def expReActivity (N_c : ℕ)
    (c : ConcretePlaquette d N → ℂ) :
    GaugeConfig d N (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) →
      ConcretePlaquette d N → ℝ :=
  fun A p => Real.exp ((2 : ℝ) * (c p * Matrix.trace (wilsonLine A
    (plaquetteList (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val).re) - 1

open Classical in
/-- **(V4-0 i) The exact Wilson activity is a local weight.** -/
theorem isLocalWeight_expReActivity (N_c : ℕ) [NeZero N_c]
    (c : ConcretePlaquette d N → ℂ) :
    IsLocalWeight (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
      (expReActivity N_c c) := by
  intro p A A' h
  have hre : (2 : ℝ) * (c p * Matrix.trace (wilsonLine A
      (plaquetteList (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val).re
    = (2 : ℝ) * (c p * Matrix.trace (wilsonLine A'
      (plaquetteList (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val).re :=
    isLocalWeight_reActivity (d := d) (N := N) N_c c p A A' h
  show Real.exp ((2 : ℝ) * (c p * Matrix.trace (wilsonLine A
      (plaquetteList (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val).re) - 1
    = Real.exp ((2 : ℝ) * (c p * Matrix.trace (wilsonLine A'
      (plaquetteList (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val).re) - 1
  rw [hre]

open Classical in
/-- **(V4-0 ii) The exact Wilson activity is measurable.** -/
theorem measurable_expReActivity (N_c : ℕ) [NeZero N_c]
    (c : ConcretePlaquette d N → ℂ) :
    ∀ p : ConcretePlaquette d N,
      Measurable (fun A : GaugeConfig d N
        (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) =>
        expReActivity N_c c A p) :=
  fun p => (Real.measurable_exp.comp
    (measurable_reActivity (d := d) (N := N) N_c c p)).sub measurable_const

open Classical in
/-- **(V4-0 iii) The exact Wilson activity is uniformly bounded** by
`exp(2δN_c) − 1` — by the elementary `|e^w − 1| ≤ e^B − 1` for
`|w| ≤ B` (AM–GM: `2 ≤ e^B + e^{−B}`). -/
theorem expReActivity_bound (N_c : ℕ) [NeZero N_c]
    {δ : ℝ} (c : ConcretePlaquette d N → ℂ) (hc : ∀ p, ‖c p‖ ≤ δ) :
    ∀ (A : GaugeConfig d N (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))
      (p : ConcretePlaquette d N),
      |expReActivity N_c c A p| ≤ Real.exp (2 * δ * (N_c : ℝ)) - 1 := by
  intro A p
  set w : ℝ := (2 : ℝ) * (c p * Matrix.trace (wilsonLine A
    (plaquetteList (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val).re with hw
  set B : ℝ := 2 * δ * (N_c : ℝ) with hB
  have hwB : |w| ≤ B := reActivity_bound (d := d) (N := N) N_c c hc A p
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) hwB
  show |Real.exp w - 1| ≤ Real.exp B - 1
  rw [abs_le]
  have hwle : w ≤ B := le_trans (le_abs_self _) hwB
  have hnwle : -B ≤ w := neg_le_of_abs_le hwB
  constructor
  · -- lower: e^w - 1 ≥ -(e^B - 1), i.e. e^w + e^B ≥ 2... use e^w ≥ e^{-B} ≥ 2 - e^B
    have h1 : Real.exp (-B) ≤ Real.exp w := Real.exp_le_exp.mpr hnwle
    have h2 : (2 : ℝ) ≤ Real.exp B + Real.exp (-B) := by
      have := Real.add_one_le_exp B
      have hneg := Real.add_one_le_exp (-B)
      linarith
    have h3 : Real.exp (-B) = 1 / Real.exp B := by
      rw [Real.exp_neg]; ring
    linarith
  · -- upper: e^w - 1 ≤ e^B - 1
    have h1 : Real.exp w ≤ Real.exp B := Real.exp_le_exp.mpr hwle
    linarith

open Classical in
/-- **(V4-0 iv) The exact factor is the cast of `1 + expReActivity`.**
At the conjugate pair the ℂ Wilson factor `exp(z_p)` equals the cast of
the real `1 + (exp(z_p) − 1) = exp(z_p)`. -/
theorem exp_conjPair_eq_cast (N_c : ℕ) [NeZero N_c]
    (c : ConcretePlaquette d N → ℂ)
    (A : GaugeConfig d N (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))
    (p : ConcretePlaquette d N) :
    Complex.exp (c p * Matrix.trace (wilsonLine A
        (plaquetteList (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
      + (starRingEnd ℂ) (c p) * star (Matrix.trace (wilsonLine A
        (plaquetteList (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val))
      = ((1 + expReActivity N_c c A p : ℝ) : ℂ) := by
  have hstar : (starRingEnd ℂ) (c p) * star (Matrix.trace (wilsonLine A
      (plaquetteList (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)
      = (starRingEnd ℂ) (c p * Matrix.trace (wilsonLine A
        (plaquetteList (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val) := by
    rw [map_mul]; rfl
  rw [hstar, Complex.add_conj, expReActivity]
  rw [show (1 : ℝ) + (Real.exp ((2 : ℝ) * (c p * Matrix.trace (wilsonLine A
      (plaquetteList (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val).re) - 1)
    = Real.exp ((2 : ℝ) * (c p * Matrix.trace (wilsonLine A
      (plaquetteList (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val).re)
    from by ring]
  rw [Complex.ofReal_exp]

open Classical in
/-- **(V4-2(b) the far-factor cast)** the ℂ far factor of the exact
loop-tagged expansion at the conjugate pair IS the cast of the real
restricted `Z` of the activity `expReActivity` — the exp analog of
`integral_conjPair_prod_eq_cast`. -/
theorem integral_exp_conjPair_prod_eq_cast (N_c : ℕ) [NeZero N_c]
    (c : ConcretePlaquette d N → ℂ)
    (F : Finset (ConcretePlaquette d N)) :
    ∫ A, ∏ p ∈ F, ((1 : ℂ)
        + (Complex.exp (c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + (starRingEnd ℂ) (c p) * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)) - 1))
        ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c))
      = ((∫ A, ∏ p ∈ F, (1 + expReActivity N_c c A p)
          ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)) : ℝ) : ℂ) := by
  have hpt : (fun A : GaugeConfig d N
      (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) =>
      ∏ p ∈ F, ((1 : ℂ)
        + (Complex.exp (c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + (starRingEnd ℂ) (c p) * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)) - 1)))
      = fun A => ∏ p ∈ F, ((1 : ℂ) + ((expReActivity N_c c A p : ℝ) : ℂ)) := by
    funext A
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [show (1 : ℂ) + (Complex.exp (c p * Matrix.trace (wilsonLine A
        (plaquetteList (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
      + (starRingEnd ℂ) (c p) * star (Matrix.trace (wilsonLine A
        (plaquetteList (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)) - 1)
      = Complex.exp (c p * Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
        + (starRingEnd ℂ) (c p) * star (Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val))
      from by ring]
    rw [exp_conjPair_eq_cast N_c c A p]
    push_cast
    ring
  rw [hpt]
  exact integral_prod_one_add_ofReal (sunHaarProb N_c) _ F

open Classical in
/-- **(V4-2 integrability i)** the EXACT pinned product
`∏_{p∈S}(exp z_p − 1)` is integrable — measurable (exp of measurable)
and bounded (`‖exp z_p − 1‖ ≤ e^{2δN_c}+1` through finite products). -/
theorem integrable_exp_conjPair_prod (N_c : ℕ) [NeZero N_c]
    {δ : ℝ} (c c' : ConcretePlaquette d N → ℂ)
    (hc : ∀ p, ‖c p‖ ≤ δ) (hc' : ∀ p, ‖c' p‖ ≤ δ)
    (S : Finset (ConcretePlaquette d N)) :
    Integrable (fun A => ∏ p ∈ S,
      (Complex.exp (c p * Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
        + c' p * star (Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)) - 1))
      (gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)) := by
  classical
  have hm : Measurable (fun A : GaugeConfig d N
      (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) => ∏ p ∈ S,
      (Complex.exp (c p * Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
        + c' p * star (Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)) - 1)) :=
    Finset.measurable_prod _ fun p _ =>
      (Complex.measurable_exp.comp
        ((measurable_const.mul (measurable_trace_wilsonLine _)).add
          (measurable_const.mul (continuous_star.measurable.comp
            (measurable_trace_wilsonLine _))))).sub measurable_const
  have hb : ∀ A : GaugeConfig d N
      (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)),
      ‖∏ p ∈ S,
        (Complex.exp (c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + c' p * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)) - 1)‖
        ≤ ∏ _p ∈ S, (Real.exp (2 * δ * (N_c : ℝ)) + 1) := by
    intro A
    rw [norm_prod]
    refine Finset.prod_le_prod (fun p _ => norm_nonneg _) (fun p _ => ?_)
    have hδ0 : (0 : ℝ) ≤ δ := le_trans (norm_nonneg (c p)) (hc p)
    set z : ℂ := c p * Matrix.trace (wilsonLine A
        (plaquetteList (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
      + c' p * star (Matrix.trace (wilsonLine A
        (plaquetteList (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val) with hz
    have hznorm : ‖z‖ ≤ 2 * δ * (N_c : ℝ) := by
      rw [hz]
      have h1 : ‖c p * Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val‖
          ≤ δ * (N_c : ℝ) := by
        rw [norm_mul]
        exact mul_le_mul (hc p) (norm_trace_wilsonLine_le A _)
          (norm_nonneg _) hδ0
      have h2 : ‖c' p * star (Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)‖
          ≤ δ * (N_c : ℝ) := by
        rw [norm_mul, norm_star]
        exact mul_le_mul (hc' p) (norm_trace_wilsonLine_le A _)
          (norm_nonneg _) hδ0
      calc ‖_ + _‖ ≤ _ + _ := norm_add_le _ _
        _ ≤ 2 * δ * (N_c : ℝ) := by linarith
    have hexp : ‖Complex.exp z‖ ≤ Real.exp (2 * δ * (N_c : ℝ)) := by
      rw [Complex.norm_exp]
      exact Real.exp_le_exp.mpr (le_trans (Complex.re_le_norm z) hznorm)
    calc ‖Complex.exp z - 1‖ ≤ ‖Complex.exp z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ Real.exp (2 * δ * (N_c : ℝ)) + 1 := by rw [norm_one]; linarith
  have h2 := (integrable_const (1 : ℂ)
    (μ := gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c))).bdd_mul
    hm.aestronglyMeasurable (MeasureTheory.ae_of_all _ hb)
  simpa using h2

open Classical in
/-- **(V4-2 integrability ii)** the trace times the EXACT pinned
product is integrable. -/
theorem integrable_trace_mul_exp_conjPair_prod (N_c : ℕ) [NeZero N_c]
    (es : List (ConcreteEdge d N))
    {δ : ℝ} (c c' : ConcretePlaquette d N → ℂ)
    (hc : ∀ p, ‖c p‖ ≤ δ) (hc' : ∀ p, ‖c' p‖ ≤ δ)
    (S : Finset (ConcretePlaquette d N)) :
    Integrable (fun A => Matrix.trace (wilsonLine A es).val * ∏ p ∈ S,
      (Complex.exp (c p * Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
        + c' p * star (Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)) - 1))
      (gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)) := by
  classical
  have hm : Measurable (fun A : GaugeConfig d N
      (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) =>
      Matrix.trace (wilsonLine A es).val * ∏ p ∈ S,
      (Complex.exp (c p * Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
        + c' p * star (Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)) - 1)) :=
    (measurable_trace_wilsonLine es).mul
      (Finset.measurable_prod _ fun p _ =>
        (Complex.measurable_exp.comp
          ((measurable_const.mul (measurable_trace_wilsonLine _)).add
            (measurable_const.mul (continuous_star.measurable.comp
              (measurable_trace_wilsonLine _))))).sub measurable_const)
  have hb : ∀ A : GaugeConfig d N
      (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)),
      ‖Matrix.trace (wilsonLine A es).val * ∏ p ∈ S,
        (Complex.exp (c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + c' p * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)) - 1)‖
        ≤ (N_c : ℝ) * ∏ _p ∈ S, (Real.exp (2 * δ * (N_c : ℝ)) + 1) := by
    intro A
    rw [norm_mul]
    refine mul_le_mul (norm_trace_wilsonLine_le A es) ?_
      (norm_nonneg _) (Nat.cast_nonneg _)
    rw [norm_prod]
    refine Finset.prod_le_prod (fun p _ => norm_nonneg _) (fun p _ => ?_)
    have hδ0 : (0 : ℝ) ≤ δ := le_trans (norm_nonneg (c p)) (hc p)
    set z : ℂ := c p * Matrix.trace (wilsonLine A
        (plaquetteList (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
      + c' p * star (Matrix.trace (wilsonLine A
        (plaquetteList (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val) with hz
    have hznorm : ‖z‖ ≤ 2 * δ * (N_c : ℝ) := by
      rw [hz]
      have h1 : ‖c p * Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val‖
          ≤ δ * (N_c : ℝ) := by
        rw [norm_mul]
        exact mul_le_mul (hc p) (norm_trace_wilsonLine_le A _)
          (norm_nonneg _) hδ0
      have h2 : ‖c' p * star (Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)‖
          ≤ δ * (N_c : ℝ) := by
        rw [norm_mul, norm_star]
        exact mul_le_mul (hc' p) (norm_trace_wilsonLine_le A _)
          (norm_nonneg _) hδ0
      calc ‖_ + _‖ ≤ _ + _ := norm_add_le _ _
        _ ≤ 2 * δ * (N_c : ℝ) := by linarith
    have hexp : ‖Complex.exp z‖ ≤ Real.exp (2 * δ * (N_c : ℝ)) := by
      rw [Complex.norm_exp]
      exact Real.exp_le_exp.mpr (le_trans (Complex.re_le_norm z) hznorm)
    calc ‖Complex.exp z - 1‖ ≤ ‖Complex.exp z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ Real.exp (2 * δ * (N_c : ℝ)) + 1 := by rw [norm_one]; linarith
  have h2 := (integrable_const (1 : ℂ)
    (μ := gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c))).bdd_mul
    hm.aestronglyMeasurable (MeasureTheory.ae_of_all _ hb)
  simpa using h2

set_option maxHeartbeats 1600000 in
open Classical in
/-- **V4-2(a) — the EXACT pinned numerator bound:** the unnormalized
loop integral against the TRUE Wilson factor `∏_p exp(z_p)` is bounded
by the pinned sum of exp-dichotomy weights times the norms of the far
factors — the exp analog of `norm_integral_wilson_loop_le_pinned_sum`,
chaining the loop-tagged expansion (at activity `f_p = exp(z_p) − 1`)
with the V4-1 pinned exp dichotomy. -/
theorem norm_integral_exp_wilson_loop_le_pinned_sum
    (N_c : ℕ) [NeZero N_c]
    (es : List (ConcreteEdge d N)) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (c c' : ConcretePlaquette d N → ℂ)
    (hc : ∀ p, ‖c p‖ ≤ δ) (hc' : ∀ p, ‖c' p‖ ≤ δ) :
    ‖∫ A, Matrix.trace (wilsonLine A es).val *
        ∏ p : ConcretePlaquette d N,
          (1 + (Complex.exp (c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + c' p * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)) - 1))
        ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c))‖
      ≤ ∑ S₀ ∈ (Finset.univ :
            Finset (ConcretePlaquette d N)).powerset.filter
            (fun S₀ => nearLoop es S₀ = S₀),
          (if chainAreaA (R := ZMod N_c) (d := d) (N := N)
                (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
                (loopChain (R := ZMod N_c) (d := d) (N := N)
                  (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) es)
              ≤ S₀.card
            then (N_c : ℝ) * (Real.exp (2 * δ * (N_c : ℝ)) - 1) ^ S₀.card
            else 0) *
          ‖∫ A, ∏ p ∈ farRegion es S₀,
            (1 + (Complex.exp (c p * Matrix.trace (wilsonLine A
              (plaquetteList (d := d) (N := N)
                (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
            + c' p * star (Matrix.trace (wilsonLine A
              (plaquetteList (d := d) (N := N)
                (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)) - 1))
            ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c))‖ := by
  classical
  have hf : ∀ p : ConcretePlaquette d N,
      DependsOnPos (fun A => Complex.exp (c p * Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
        + c' p * star (Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)) - 1)
        (plaquetteSupport p) := fun p =>
    dependsOnPos_plaquette_obs'
      (fun U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) =>
        Complex.exp (c p * Matrix.trace U.val
          + c' p * star (Matrix.trace U.val)) - 1) p
  have heq := integral_wilson_loop_tagged_expansion
    (sunHaarProb N_c)
    (fun U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) =>
      Matrix.trace U.val) es
    (fun p A => Complex.exp (c p * Matrix.trace (wilsonLine A
        (plaquetteList (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
      + c' p * star (Matrix.trace (wilsonLine A
        (plaquetteList (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)) - 1)
    hf
    (fun S => integrable_trace_mul_exp_conjPair_prod N_c es c c' hc hc' S)
    (fun S => integrable_exp_conjPair_prod N_c c c' hc hc' S)
  refine le_trans (le_of_eq (congrArg norm heq)) ?_
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun S₀ _ => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (norm_integral_exp_pinned_term_le es δ hδ0 c c' hc hc' S₀)
    (norm_nonneg _)

end YangMills
