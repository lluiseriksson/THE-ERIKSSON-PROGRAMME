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

end YangMills
