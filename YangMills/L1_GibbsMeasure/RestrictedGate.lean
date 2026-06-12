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

end YangMills
