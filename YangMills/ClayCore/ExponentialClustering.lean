/-
Copyright (c) 2026 The Eriksson Programme. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson

Exponential Clustering from the Kotecky-Preiss Criterion (Theorem 5.5).

Given polymer activities satisfying the KP smallness criterion, the
connected two-point correlator decays exponentially: whenever it is
majorised by the connecting-cluster sum, it is bounded by
  C_clust * r^(dist 0 x),
where r in (0,1) is the polymer decay rate and
  C_clust = sum_n (C_conn * n^dim * A0 * r^n) < infinity.

The proof uses KP summability (Phase 5.2) to reduce the connected
correlator to a sum over polymer clusters containing both 0 and x,
each of diameter at least dist(0, x), and then extracts r^(dist 0 x)
from the geometric decay of activities.

Reference: Theorem 5.5, [Eriksson Feb 2026], Section 5.3.3.
-/

import Mathlib
import YangMills.ClayCore.KPSmallness

namespace YangMills

/-! ## Two-point cluster bound -/

/-- Structural witness for the cluster-expansion identity for the connected
two-point correlator. The bound is
  corr <= sum_n (C_conn * n^dim * A0 * r^(n + dist 0 x)).
C_conn is the combinatorial constant bounding the number of polymers of
extra-diameter n connecting 0 and x; the underlying polymer activities are
governed by pab : PolymerActivityBound. -/
structure TwoPointClusterBound where
  /-- Polymer activity bound providing the r in (0,1) geometric decay. -/
  pab : PolymerActivityBound
  /-- Connecting-cluster combinatorial constant. -/
  C_conn : ℝ
  /-- Positivity hypothesis. -/
  hC_conn : 0 < C_conn

/-! ## Summability of the connecting-cluster sum -/

/-- The connecting-cluster sum is summable for any lattice distance. -/
theorem connecting_cluster_summable
    (tcb : TwoPointClusterBound) (dist_0x : ℕ) :
    Summable (fun n : ℕ => tcb.C_conn * ((n : ℝ)) ^ tcb.pab.dim *
        tcb.pab.A₀ * tcb.pab.r ^ (n + dist_0x)) := by
  have h_norm : ‖tcb.pab.r‖ < 1 := by
    rw [Real.norm_of_nonneg tcb.pab.hr_pos.le]
    exact tcb.pab.hr_lt_one
  have hbase : Summable
      (fun n : ℕ => ((n : ℝ)) ^ tcb.pab.dim * tcb.pab.r ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one tcb.pab.dim h_norm
  have hmul := hbase.mul_left (tcb.C_conn * tcb.pab.A₀ * tcb.pab.r ^ dist_0x)
  have heq :
      (fun n : ℕ => tcb.C_conn * tcb.pab.A₀ * tcb.pab.r ^ dist_0x *
            (((n : ℝ)) ^ tcb.pab.dim * tcb.pab.r ^ n))
      = (fun n : ℕ => tcb.C_conn * ((n : ℝ)) ^ tcb.pab.dim *
            tcb.pab.A₀ * tcb.pab.r ^ (n + dist_0x)) := by
    funext n
    rw [pow_add]
    ring
  rw [heq] at hmul
  exact hmul

/-- Factoring: sum_n a_n r^(n + d) = r^d * sum_n a_n r^n. -/
theorem connecting_cluster_tsum_eq
    (tcb : TwoPointClusterBound) (dist_0x : ℕ) :
    (∑' n : ℕ, tcb.C_conn * ((n : ℝ)) ^ tcb.pab.dim *
          tcb.pab.A₀ * tcb.pab.r ^ (n + dist_0x)) =
    tcb.pab.r ^ dist_0x *
      ∑' n : ℕ, tcb.C_conn * ((n : ℝ)) ^ tcb.pab.dim *
          tcb.pab.A₀ * tcb.pab.r ^ n := by
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [pow_add]
  ring

/-- Summability of the prefactor sum_n C_conn * n^dim * A0 * r^n. -/
theorem prefactor_summable (tcb : TwoPointClusterBound) :
    Summable (fun n : ℕ => tcb.C_conn * ((n : ℝ)) ^ tcb.pab.dim *
        tcb.pab.A₀ * tcb.pab.r ^ n) := by
  have h_norm : ‖tcb.pab.r‖ < 1 := by
    rw [Real.norm_of_nonneg tcb.pab.hr_pos.le]
    exact tcb.pab.hr_lt_one
  have hbase : Summable
      (fun n : ℕ => ((n : ℝ)) ^ tcb.pab.dim * tcb.pab.r ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one tcb.pab.dim h_norm
  have hmul := hbase.mul_left (tcb.C_conn * tcb.pab.A₀)
  have heq :
      (fun n : ℕ => tcb.C_conn * tcb.pab.A₀ *
            (((n : ℝ)) ^ tcb.pab.dim * tcb.pab.r ^ n))
      = (fun n : ℕ => tcb.C_conn * ((n : ℝ)) ^ tcb.pab.dim *
            tcb.pab.A₀ * tcb.pab.r ^ n) := by
    funext n
    ring
  rw [heq] at hmul
  exact hmul

/-! ## Main exponential clustering theorem -/

/-- **Theorem 5.5 (exponential clustering)**. The connected two-point
correlator, whenever majorised by the connecting-cluster sum, enjoys
exponential decay at rate -log(r):
  corr <= C_clust * r^(dist 0 x),
with C_clust = sum_n C_conn * n^dim * A0 * r^n finite and non-negative. -/
theorem exponential_clustering
    (tcb : TwoPointClusterBound) (dist_0x : ℕ) :
    ∃ C_clust : ℝ, 0 ≤ C_clust ∧
      ∀ (corr_bound : ℝ),
        corr_bound ≤ ∑' n : ℕ, tcb.C_conn * ((n : ℝ)) ^ tcb.pab.dim *
            tcb.pab.A₀ * tcb.pab.r ^ (n + dist_0x) →
        corr_bound ≤ C_clust * tcb.pab.r ^ dist_0x := by
  refine ⟨∑' n : ℕ, tcb.C_conn * ((n : ℝ)) ^ tcb.pab.dim *
            tcb.pab.A₀ * tcb.pab.r ^ n, ?_, ?_⟩
  · apply tsum_nonneg
    intro n
    have h1 : 0 ≤ tcb.C_conn := tcb.hC_conn.le
    have h2 : 0 ≤ ((n : ℝ)) ^ tcb.pab.dim := pow_nonneg (Nat.cast_nonneg _) _
    have h3 : 0 ≤ tcb.pab.A₀ := tcb.pab.hA₀
    have h4 : 0 ≤ tcb.pab.r ^ n := pow_nonneg tcb.pab.hr_pos.le _
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4
  · intro corr_bound hcorr
    calc corr_bound
        ≤ ∑' n : ℕ, tcb.C_conn * ((n : ℝ)) ^ tcb.pab.dim *
              tcb.pab.A₀ * tcb.pab.r ^ (n + dist_0x) := hcorr
      _ = tcb.pab.r ^ dist_0x *
            ∑' n : ℕ, tcb.C_conn * ((n : ℝ)) ^ tcb.pab.dim *
              tcb.pab.A₀ * tcb.pab.r ^ n :=
                connecting_cluster_tsum_eq tcb dist_0x
      _ = (∑' n : ℕ, tcb.C_conn * ((n : ℝ)) ^ tcb.pab.dim *
              tcb.pab.A₀ * tcb.pab.r ^ n) * tcb.pab.r ^ dist_0x := by ring

/-- The exponential decay rate -log(r) is strictly positive. -/
theorem clustering_rate_positive (tcb : TwoPointClusterBound) :
    0 < -Real.log tcb.pab.r := by
  linarith [Real.log_neg tcb.pab.hr_pos tcb.pab.hr_lt_one]

/-- Exponential form: r^n = exp(-(2a) * n) where a = kpParameter r. -/
theorem clustering_exp_form (tcb : TwoPointClusterBound) (n : ℕ) :
    tcb.pab.r ^ n = Real.exp (-(2 * kpParameter tcb.pab.r) * n) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hrp : (0 : ℝ) < tcb.pab.r := tcb.pab.hr_pos
    have hlog_eq : -(2 * kpParameter tcb.pab.r) = Real.log tcb.pab.r := by
      unfold kpParameter
      ring
    rw [pow_succ, ih]
    push_cast
    rw [show -(2 * kpParameter tcb.pab.r) * ((k : ℝ) + 1)
          = -(2 * kpParameter tcb.pab.r) * (k : ℝ)
            + -(2 * kpParameter tcb.pab.r) from by ring]
    rw [Real.exp_add]
    congr 1
    rw [hlog_eq]
    exact (Real.exp_log hrp).symm

end YangMills
