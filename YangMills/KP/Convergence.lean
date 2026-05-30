/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.KP.Criterion

/-!
# KP2b / Target B (back-half) — convergence from a per-size cluster bound

The Kotecký–Preiss convergence theorem (`docs/kp-cluster-expansion-plan.md`, Target B /
E4) bounds the cluster sum under the smallness criterion.  Its hard core is the
**per-cluster-size estimate** obtained from the tree-graph inequality: the total weight
of clusters of size `n` (containing a fixed polymer) decays geometrically.  That estimate
is *not* in Mathlib (no spanning-tree / tree-graph API) and is the genuine open content.

This file proves the **back-half**, exactly parallel to Target A's
`closed_form_of_recurrence`: *granting* a geometric per-size bound `b n ≤ C·r^n` with
`0 ≤ r < 1`, the cluster series `∑ b n` is summable with sum `≤ C/(1−r)`.  Combined with
the (open) tree-graph estimate this yields KP convergence — so Target B is reduced to that
single estimate, with no axiom introduced (the bound enters as an explicit hypothesis).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.KP

open scoped BigOperators

/-- **Back-half of Target B: a geometric per-size bound gives absolute convergence.**
If the size-`n` cluster contribution `b n` is nonnegative and dominated by `C·r^n` with
`0 ≤ r < 1` (the conclusion of the open tree-graph estimate), then the cluster series is
summable.  This isolates Target B's open content to that single geometric estimate. -/
theorem cluster_series_summable (b : ℕ → ℝ) (C r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hb0 : ∀ n, 0 ≤ b n)
    (hbound : ∀ n, b n ≤ C * r ^ n) :
    Summable b := by
  have hgeom : Summable (fun n => C * r ^ n) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left C
  exact Summable.of_nonneg_of_le hb0 hbound hgeom

/-- **Back-half of Target B (quantitative): the cluster sum is bounded by `C/(1−r)`.**
Under the same geometric per-size bound, the total cluster sum is controlled by the
closed-form geometric tail `C/(1−r)`.  This is the explicit convergence bound the KP
theorem delivers (the `m*` mass-gap rate ultimately comes from such a tail). -/
theorem cluster_sum_le (b : ℕ → ℝ) (C r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hb0 : ∀ n, 0 ≤ b n)
    (hbound : ∀ n, b n ≤ C * r ^ n) :
    ∑' n, b n ≤ C / (1 - r) := by
  have hgeom : Summable (fun n => C * r ^ n) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left C
  have hsum : Summable b := Summable.of_nonneg_of_le hb0 hbound hgeom
  have hle : ∑' n, b n ≤ ∑' n, C * r ^ n := hsum.tsum_le_tsum hbound hgeom
  have heq : ∑' n, C * r ^ n = C / (1 - r) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]
  rwa [heq] at hle

/-- **Analytic core of E3's single-polymer case: the Mayer log series.**
For `|z| < 1`, the alternating series `∑ₙ (−1)ⁿ·zⁿ⁺¹/(n+1)` sums to `log(1 + z)`.
This is exactly the shape the single-polymer cluster sum collapses to once Target A's
`ursellComplete (n+1) = (−1)ⁿ·n!` is in hand: a one-polymer term is
`(1/(n+1)!)·φ(K_{n+1})·zⁿ⁺¹ = (−1)ⁿ/(n+1)·zⁿ⁺¹`, whose total is `log(1+z)`.  So the
single-polymer identity `clusterSum = log(1 + z(X))` (the `n=1` case of
`Ξ = exp(clusterSum)`) reduces to Target A plus this lemma — proved here directly from
Mathlib's log power series via `x ↦ −z`. -/
theorem mayer_log_series {z : ℝ} (h : |z| < 1) :
    HasSum (fun n : ℕ => (-1) ^ n * z ^ (n + 1) / ((n : ℝ) + 1)) (Real.log (1 + z)) := by
  have hx : |(-z)| < 1 := by rwa [abs_neg]
  have hfun : (fun n : ℕ => (-1) ^ n * z ^ (n + 1) / ((n : ℝ) + 1))
            = (fun n : ℕ => -((-z) ^ (n + 1) / ((n : ℝ) + 1))) := by
    funext n; rw [neg_pow]; ring
  have hval : Real.log (1 + z) = -(-Real.log (1 - -z)) := by
    rw [sub_neg_eq_add, neg_neg]
  rw [hfun, hval]
  exact (Real.hasSum_pow_div_log_of_abs_lt_one hx).neg

end YangMills.KP
