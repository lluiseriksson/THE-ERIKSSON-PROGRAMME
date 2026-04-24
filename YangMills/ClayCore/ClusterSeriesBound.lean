/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.ClayCore.PolymerDiameterBound
import YangMills.ClayCore.KPSmallness

/-!
# Phase 15b: Cluster series convergence (D1 + D2)

Oracle target: `[propext, Classical.choice, Quot.sound]`.

* **D1** `connecting_cluster_tsum_summable` — Summability of
  `n ↦ C·n^dim·A₀·r^(n+d)` for `0 < r < 1`.
* **D2** `connecting_cluster_tsum_le` — The tsum factors as
  `clusterPrefactor r C A₀ dim · r^d`.
-/

namespace YangMills

open Real

/-! ### Helpers -/

/-- Split a geometric power across an additive exponent. -/
theorem pow_add_factor (r : ℝ) (n dist : ℕ) :
    r ^ (n + dist) = r ^ n * r ^ dist := pow_add r n dist

/-- Summability of `n ↦ n^dim · r^n` for `0 < r < 1`. Internal helper. -/
private theorem summable_pow_mul_geometric
    (r : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1) (dim : ℕ) :
    Summable (fun n : ℕ => (n : ℝ) ^ dim * r ^ n) := by
  have hr_norm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hr_pos]; exact hr_lt1
  have hnorm :=
    summable_norm_pow_mul_geometric_of_norm_lt_one (R := ℝ) dim hr_norm
  simp only [Real.norm_eq_abs, abs_mul, abs_pow, Nat.abs_cast,
    abs_of_pos hr_pos] at hnorm
  exact hnorm

/-! ### D1: Summability of the connecting-cluster series -/

/-- **D1.** The connecting-cluster series `∑ n, C·n^dim·A₀·r^(n+d)`
is summable whenever `0 < r < 1`. -/
theorem connecting_cluster_tsum_summable
    (r : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (C_conn A₀ : ℝ) (dim dist_0x : ℕ) :
    Summable (fun n : ℕ =>
        C_conn * (n : ℝ) ^ dim * A₀ * r ^ (n + dist_0x)) := by
  have hbase := summable_pow_mul_geometric r hr_pos hr_lt1 dim
  have goal_eq :
      (fun n : ℕ => C_conn * (n : ℝ) ^ dim * A₀ * r ^ (n + dist_0x)) =
      (fun n : ℕ =>
        (C_conn * A₀ * r ^ dist_0x) * ((n : ℝ) ^ dim * r ^ n)) := by
    funext n; rw [pow_add]; ring
  rw [goal_eq]
  exact hbase.mul_left _

/-- The connecting-cluster summand is nonnegative when the physical
constants are positive. -/
theorem connecting_cluster_summand_nonneg
    (r : ℝ) (hr_pos : 0 < r)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (dim dist_0x n : ℕ) :
    0 ≤ C_conn * (n : ℝ) ^ dim * A₀ * r ^ (n + dist_0x) := by
  positivity

/-- Any finite partial sum of the nonnegative connecting-cluster series is
bounded by its `tsum`. -/
theorem connecting_cluster_partial_sum_le_tsum
    (r : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (dim dist_0x M : ℕ) :
    Finset.sum (Finset.range M) (fun n : ℕ =>
        C_conn * (n : ℝ) ^ dim * A₀ * r ^ (n + dist_0x)) ≤
      ∑' n : ℕ, C_conn * (n : ℝ) ^ dim * A₀ *
        r ^ (n + dist_0x) := by
  exact (connecting_cluster_tsum_summable r hr_pos hr_lt1 C_conn A₀ dim dist_0x).sum_le_tsum
    (Finset.range M)
    (fun n _ => connecting_cluster_summand_nonneg r hr_pos C_conn A₀ hC hA dim dist_0x n)

/-! ### D2: Tsum factoring -/

/-- The tsum factors through the `r^dist_0x` prefactor. -/
theorem connecting_cluster_tsum_eq_factored
    (r : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (C_conn A₀ : ℝ) (dim dist_0x : ℕ) :
    ∑' n : ℕ, C_conn * (n : ℝ) ^ dim * A₀ * r ^ (n + dist_0x) =
    C_conn * A₀ * (∑' n : ℕ, (n : ℝ) ^ dim * r ^ n) * r ^ dist_0x := by
  have goal_eq :
      (fun n : ℕ => C_conn * (n : ℝ) ^ dim * A₀ * r ^ (n + dist_0x)) =
      (fun n : ℕ =>
        (C_conn * A₀ * r ^ dist_0x) * ((n : ℝ) ^ dim * r ^ n)) := by
    funext n; rw [pow_add]; ring
  rw [goal_eq, tsum_mul_left]
  ring

/-- Strict positivity of the inner polynomial–geometric tsum. -/
theorem inner_sum_pos
    (r : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1) (dim : ℕ) :
    0 < ∑' n : ℕ, (n : ℝ) ^ dim * r ^ n := by
  have hsum := summable_pow_mul_geometric r hr_pos hr_lt1 dim
  refine Summable.tsum_pos hsum ?_ 1 ?_
  · intro n; positivity
  · simp [hr_pos]

/-- Prefactor extracted from the connecting-cluster tsum. -/
noncomputable def clusterPrefactor
    (r : ℝ) (C_conn A₀ : ℝ) (dim : ℕ) : ℝ :=
  C_conn * A₀ * ∑' n : ℕ, (n : ℝ) ^ dim * r ^ n

/-- The prefactor is strictly positive when the inputs are. -/
theorem clusterPrefactor_pos
    (r : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀) (dim : ℕ) :
    0 < clusterPrefactor r C_conn A₀ dim := by
  unfold clusterPrefactor
  exact mul_pos (mul_pos hC hA) (inner_sum_pos r hr_pos hr_lt1 dim)

/-- **D2.** The connecting-cluster tsum factors as
`clusterPrefactor r C A₀ dim · r^dist_0x`. -/
theorem connecting_cluster_tsum_le
    (r : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (dim dist_0x : ℕ) :
    ∑' n : ℕ, C_conn * (n : ℝ) ^ dim * A₀ * r ^ (n + dist_0x) =
    clusterPrefactor r C_conn A₀ dim * r ^ dist_0x := by
  rw [connecting_cluster_tsum_eq_factored r hr_pos hr_lt1]
  unfold clusterPrefactor
  ring

/-! ### Bridge to the KP parameter -/

/-- For `0 < r`, `r^dist = exp(-(kpParameter r) · dist · 2)`,
using `kpParameter r = -log r / 2`. -/
theorem rpow_eq_exp_kpParameter
    (r : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1) (dist : ℕ) :
    (r : ℝ) ^ dist = Real.exp (-(kpParameter r) * (dist : ℝ) * 2) := by
  unfold kpParameter
  rw [show -(-Real.log r / 2) * (dist : ℝ) * 2 = (dist : ℝ) * Real.log r by ring,
      Real.exp_nat_mul, Real.exp_log hr_pos]

#print axioms connecting_cluster_summand_nonneg
#print axioms connecting_cluster_partial_sum_le_tsum

end YangMills
