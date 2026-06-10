/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.KP.SharpShell

/-!
# Cluster tails — activity tilting and the size-tail bound

Half A of `docs/CLUSTER-CORRELATION-PLAN.md`: the decay engine for the
cluster-correlation chain.

* `PolymerSystem.tilt P w` — same polymers and incompatibilities,
  activities rescaled by `e^{w(c)}`;
* `pinnedClusterWeightGE P sz c L n` — the pinned per-size weight
  restricted to clusters of total `sz`-size at least `L`;
* `pinnedClusterWeightGE_le_tilt` — the per-size comparison: restricted
  weights are `e^{-εL}` times tilted pinned weights;
* **`kp_pinned_cluster_tail_bound`** — under the bare KP criterion FOR
  THE TILTED SYSTEM, the total restricted pinned sum is bounded by
  `e^{-εL}·e^{ε·sz(c)}·‖z(c)‖·e^{a(c)}` — exponential decay in `L`.

Clusters connecting two distant regions have large total size (Half B,
geometry), so this is the IR decay mechanism.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.KP

open scoped BigOperators

/-- **Activity tilting:** same polymers, same hard core, activities
rescaled by `e^{w(c)}`. -/
noncomputable def PolymerSystem.tilt (P : PolymerSystem)
    (w : P.Polymer → ℝ) : PolymerSystem where
  Polymer := P.Polymer
  incomp := P.incomp
  incomp_symm := P.incomp_symm
  incomp_self := P.incomp_self
  activity := fun c => (Real.exp (w c) : ℂ) * P.activity c

instance (P : PolymerSystem) (w : P.Polymer → ℝ) [Fintype P.Polymer] :
    Fintype (P.tilt w).Polymer :=
  inferInstanceAs (Fintype P.Polymer)

/-- Tilting does not change the Ursell coefficient (it only reads the
incompatibility structure). -/
lemma tilt_ursell (P : PolymerSystem) (w : P.Polymer → ℝ) {n : ℕ}
    (X : Fin n → P.Polymer) :
    ursell (P.tilt w) X = ursell P X := rfl

/-- The norm of a tilted activity. -/
lemma tilt_norm_activity (P : PolymerSystem) (w : P.Polymer → ℝ)
    (c : P.Polymer) :
    ‖(P.tilt w).activity c‖ = Real.exp (w c) * ‖P.activity c‖ := by
  show ‖(Real.exp (w c) : ℂ) * P.activity c‖ = _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

open Classical in
/-- The pinned per-size cluster weight **restricted to large clusters**:
only tuples whose total `sz`-size is at least `L` contribute. -/
noncomputable def pinnedClusterWeightGE (P : PolymerSystem)
    [Fintype P.Polymer] (sz : P.Polymer → ℕ) (c : P.Polymer)
    (L n : ℕ) : ℝ :=
  (((n + 1).factorial : ℝ))⁻¹ *
    ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → P.Polymer)).filter
      (fun X => X 0 = c ∧ L ≤ ∑ i, sz (X i)),
      |((ursell P X : ℤ) : ℝ)| * ∏ i, ‖P.activity (X i)‖

open Classical in
lemma pinnedClusterWeightGE_nonneg (P : PolymerSystem)
    [Fintype P.Polymer] (sz : P.Polymer → ℕ) (c : P.Polymer)
    (L n : ℕ) : 0 ≤ pinnedClusterWeightGE P sz c L n := by
  unfold pinnedClusterWeightGE
  refine mul_nonneg (by positivity)
    (Finset.sum_nonneg fun X _ => ?_)
  exact mul_nonneg (abs_nonneg _)
    (Finset.prod_nonneg fun i _ => norm_nonneg _)

set_option maxHeartbeats 800000 in
open Classical in
/-- **Per-size tail comparison:** the restricted pinned weight is
`e^{-εL}` times the pinned weight of the `ε·sz`-tilted system —
each large cluster pays `e^{ε(∑ sz − L)} ≥ 1`. -/
lemma pinnedClusterWeightGE_le_tilt (P : PolymerSystem)
    [Fintype P.Polymer] (sz : P.Polymer → ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (c : P.Polymer) (L n : ℕ) :
    pinnedClusterWeightGE P sz c L n
    ≤ Real.exp (-(ε * L)) *
        pinnedClusterWeight (P.tilt fun x => ε * (sz x : ℝ)) c n := by
  unfold pinnedClusterWeightGE pinnedClusterWeight
  have key : ∑ X ∈ (Finset.univ :
      Finset (Fin (n + 1) → P.Polymer)).filter
      (fun X => X 0 = c ∧ L ≤ ∑ i, sz (X i)),
      |((ursell P X : ℤ) : ℝ)| * ∏ i, ‖P.activity (X i)‖
      ≤ Real.exp (-(ε * L)) *
        ∑ X ∈ (Finset.univ :
          Finset (Fin (n + 1) → P.Polymer)).filter
          (fun X => X 0 = c),
          |((ursell (P.tilt fun x => ε * (sz x : ℝ)) X : ℤ) : ℝ)|
            * ∏ i, ‖(P.tilt fun x => ε * (sz x : ℝ)).activity (X i)‖ := by
    have hperX : ∀ X ∈ (Finset.univ :
        Finset (Fin (n + 1) → P.Polymer)).filter
        (fun X => X 0 = c ∧ L ≤ ∑ i, sz (X i)),
        |((ursell P X : ℤ) : ℝ)| * ∏ i, ‖P.activity (X i)‖
        ≤ Real.exp (-(ε * L)) *
          (|((ursell P X : ℤ) : ℝ)|
            * ∏ i, ‖(P.tilt fun x => ε * (sz x : ℝ)).activity (X i)‖) := by
      intro X hX
      have hL : (L : ℝ) ≤ ∑ i, (sz (X i) : ℝ) := by
        have := (Finset.mem_filter.mp hX).2.2
        exact_mod_cast this
      have hprod : ∏ i, ‖(P.tilt fun x => ε * (sz x : ℝ)).activity (X i)‖
          = Real.exp (ε * ∑ i, (sz (X i) : ℝ))
            * ∏ i, ‖P.activity (X i)‖ := by
        calc ∏ i, ‖(P.tilt fun x => ε * (sz x : ℝ)).activity (X i)‖
            = ∏ i, (Real.exp (ε * (sz (X i) : ℝ))
                * ‖P.activity (X i)‖) :=
              Finset.prod_congr rfl fun i _ =>
                tilt_norm_activity P _ (X i)
          _ = (∏ i, Real.exp (ε * (sz (X i) : ℝ)))
                * ∏ i, ‖P.activity (X i)‖ :=
              Finset.prod_mul_distrib
          _ = Real.exp (ε * ∑ i, (sz (X i) : ℝ))
                * ∏ i, ‖P.activity (X i)‖ := by
              rw [← Real.exp_sum, Finset.mul_sum]
      have hexp : Real.exp (ε * L)
          ≤ Real.exp (ε * ∑ i, (sz (X i) : ℝ)) :=
        Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left hL hε)
      have hznn : (0 : ℝ) ≤ ∏ i, ‖P.activity (X i)‖ :=
        Finset.prod_nonneg fun i _ => norm_nonneg _
      calc |((ursell P X : ℤ) : ℝ)| * ∏ i, ‖P.activity (X i)‖
          = Real.exp (-(ε * L)) * (Real.exp (ε * L)
              * (|((ursell P X : ℤ) : ℝ)|
                * ∏ i, ‖P.activity (X i)‖)) := by
            rw [← mul_assoc, ← Real.exp_add]
            simp
        _ ≤ Real.exp (-(ε * L)) * (Real.exp (ε * ∑ i, (sz (X i) : ℝ))
              * (|((ursell P X : ℤ) : ℝ)|
                * ∏ i, ‖P.activity (X i)‖)) := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
            refine mul_le_mul_of_nonneg_right hexp ?_
            exact mul_nonneg (abs_nonneg _) hznn
        _ = Real.exp (-(ε * L)) *
              (|((ursell P X : ℤ) : ℝ)|
                * ∏ i, ‖(P.tilt fun x => ε * (sz x : ℝ)).activity (X i)‖)
            := by rw [hprod]; ring
    refine le_trans (Finset.sum_le_sum hperX) ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun X _ _ => ?_)
      (Real.exp_pos _).le
    · intro X hX
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp hX).2.1⟩
    · exact mul_nonneg (abs_nonneg _)
        (Finset.prod_nonneg fun i _ => norm_nonneg _)
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left key
    (by positivity : (0 : ℝ) ≤ (((n + 1).factorial : ℝ))⁻¹)

open Classical in
/-- **THE SIZE-TAIL BOUND (A†, Half A endpoint):** under the bare KP
criterion for the `ε·sz`-tilted system, the pinned cluster sums
restricted to clusters of total size ≥ `L` decay exponentially in `L`,
uniformly in the truncation. -/
theorem kp_pinned_cluster_tail_bound (P : PolymerSystem)
    [Fintype P.Polymer] (sz : P.Polymer → ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    {a : (P.tilt fun x => ε * (sz x : ℝ)).Polymer → ℝ}
    (h : KPCriterion (P.tilt fun x => ε * (sz x : ℝ)) a)
    (c : P.Polymer) (L N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), pinnedClusterWeightGE P sz c L n
    ≤ Real.exp (-(ε * L)) *
        (Real.exp (ε * (sz c : ℝ)) * ‖P.activity c‖ * Real.exp (a c)) := by
  classical
  calc ∑ n ∈ Finset.range (N + 1), pinnedClusterWeightGE P sz c L n
      ≤ ∑ n ∈ Finset.range (N + 1), Real.exp (-(ε * L)) *
          pinnedClusterWeight (P.tilt fun x => ε * (sz x : ℝ)) c n :=
        Finset.sum_le_sum fun n _ =>
          pinnedClusterWeightGE_le_tilt P sz hε c L n
    _ = Real.exp (-(ε * L)) * ∑ n ∈ Finset.range (N + 1),
          pinnedClusterWeight (P.tilt fun x => ε * (sz x : ℝ)) c n :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ Real.exp (-(ε * L)) *
          (‖(P.tilt fun x => ε * (sz x : ℝ)).activity c‖
            * Real.exp (a c)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        exact kp_pinned_cluster_bound
          (P.tilt fun x => ε * (sz x : ℝ)) h c N
    _ = Real.exp (-(ε * L)) *
          (Real.exp (ε * (sz c : ℝ)) * ‖P.activity c‖
            * Real.exp (a c)) := by
        rw [tilt_norm_activity]

open Classical in
/-- **Summed size-tail bound:** the restricted pinned series converges
with `∑' ≤ e^{-εL}·e^{ε·sz(c)}·‖z(c)‖·e^{a(c)}` — the form the
covariance chain (Half B) consumes. -/
theorem pinned_cluster_tail_summable (P : PolymerSystem)
    [Fintype P.Polymer] (sz : P.Polymer → ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    {a : (P.tilt fun x => ε * (sz x : ℝ)).Polymer → ℝ}
    (h : KPCriterion (P.tilt fun x => ε * (sz x : ℝ)) a)
    (c : P.Polymer) (L : ℕ) :
    Summable (fun n => pinnedClusterWeightGE P sz c L n) ∧
    ∑' n, pinnedClusterWeightGE P sz c L n
      ≤ Real.exp (-(ε * L)) *
          (Real.exp (ε * (sz c : ℝ)) * ‖P.activity c‖
            * Real.exp (a c)) := by
  classical
  have hb : ∀ M : ℕ,
      ∑ n ∈ Finset.range M, pinnedClusterWeightGE P sz c L n
      ≤ Real.exp (-(ε * L)) *
          (Real.exp (ε * (sz c : ℝ)) * ‖P.activity c‖
            * Real.exp (a c)) := by
    intro M
    match M with
    | 0 =>
        simp only [Finset.range_zero, Finset.sum_empty]
        positivity
    | M + 1 => exact kp_pinned_cluster_tail_bound P sz hε h c L M
  have hsum : Summable (fun n => pinnedClusterWeightGE P sz c L n) :=
    summable_of_sum_range_le
      (fun n => pinnedClusterWeightGE_nonneg P sz c L n) hb
  exact ⟨hsum, Real.tsum_le_of_sum_range_le
    (fun n => pinnedClusterWeightGE_nonneg P sz c L n) hb⟩

end YangMills.KP
