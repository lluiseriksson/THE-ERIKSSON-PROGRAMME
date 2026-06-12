/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.KP.Expansion
import YangMills.KP.Convergence

/-!
# T2 (front glue) — the concrete per-size cluster weight controls `clusterSum`

Target B's back-half (`cluster_series_summable`, `cluster_sum_le` in
`Convergence.lean`) is stated for an *abstract* sequence `b : ℕ → ℝ`.  This file
supplies the missing glue to the *concrete* Mayer object `clusterSum`
(`Expansion.lean`):

* `clusterWeight P n` — the absolute (norm-level) weight of the size-`(n+1)`
  tuples: `(1/(n+1)!) · ∑_X |φ(X)| · ∏ᵢ ‖z(Xᵢ)‖`;
* `norm_clusterTerm_le` — each complex term of the `clusterSum` series is
  norm-bounded by its weight (triangle inequality + multiplicativity of `‖·‖`);
* `clusterSum_summable_of_geometric` — a geometric bound
  `clusterWeight P n ≤ C·rⁿ` (`0 ≤ r < 1`) makes the defining series of
  `clusterSum` absolutely summable;
* `norm_clusterSum_le` — and bounds the cluster sum itself: `‖clusterSum P‖ ≤ C/(1−r)`.

With this glue, **Target B is reduced to one precisely-stated open estimate**:

  `KPCriterion P a → ∀ n, clusterWeight P n ≤ C·rⁿ`  (for some `0 ≤ r < 1`),

which is the Penrose tree-graph inequality + spanning-tree counting
(`docs/HANDOFF-KP.md`, Target B).  That estimate is carried as an explicit
hypothesis here — never an axiom.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.KP

open scoped BigOperators

variable (P : PolymerSystem)

/-- The **per-size absolute cluster weight**: the norm-level majorant of the
size-`(n+1)` term of `clusterSum`,
`(1/(n+1)!) · ∑_{X : Fin (n+1) → Polymer} |φ(X)| · ∏ᵢ ‖z(Xᵢ)‖`.
The open tree-graph estimate (Target B) asserts this decays geometrically under
the KP criterion. -/
noncomputable def clusterWeight [Fintype P.Polymer] (n : ℕ) : ℝ :=
  (((n + 1).factorial : ℝ))⁻¹ *
    ∑ X : Fin (n + 1) → P.Polymer,
      |((ursell P X : ℤ) : ℝ)| * ∏ i, ‖P.activity (X i)‖

lemma clusterWeight_nonneg [Fintype P.Polymer] (n : ℕ) :
    0 ≤ clusterWeight P n := by
  unfold clusterWeight
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun X _ => ?_)
  exact mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)

/-- **Term-wise norm bound.**  The `n`-th complex term of the `clusterSum`
series is bounded in norm by `clusterWeight P n`. -/
lemma norm_clusterTerm_le [Fintype P.Polymer] (n : ℕ) :
    ‖(((n + 1).factorial : ℂ))⁻¹ *
        ∑ X : Fin (n + 1) → P.Polymer,
          (ursell P X : ℂ) * ∏ i, P.activity (X i)‖
      ≤ clusterWeight P n := by
  unfold clusterWeight
  rw [norm_mul]
  have hfac : ‖(((n + 1).factorial : ℂ))⁻¹‖ = (((n + 1).factorial : ℝ))⁻¹ := by
    rw [norm_inv]
    congr 1
    rw [show (((n + 1).factorial : ℂ)) = (((n + 1).factorial : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n + 1).factorial : ℝ))]
  rw [hfac]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans (norm_sum_le _ _) (le_of_eq (Finset.sum_congr rfl fun X _ => ?_))
  rw [norm_mul, norm_prod]
  congr 1
  rw [show ((ursell P X : ℤ) : ℂ) = (((ursell P X : ℤ) : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_real, Real.norm_eq_abs]

/-- **Absolute convergence from a geometric weight bound.**  If the concrete
per-size cluster weight decays geometrically (the conclusion of the open
tree-graph estimate, carried as a hypothesis), the series defining
`clusterSum` is summable. -/
theorem clusterSum_summable_of_geometric [Fintype P.Polymer] (C r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hb : ∀ n, clusterWeight P n ≤ C * r ^ n) :
    Summable (fun n : ℕ => (((n + 1).factorial : ℂ))⁻¹ *
      ∑ X : Fin (n + 1) → P.Polymer,
        (ursell P X : ℂ) * ∏ i, P.activity (X i)) := by
  refine Summable.of_norm ?_
  exact cluster_series_summable _ C r hr0 hr1 (fun n => norm_nonneg _)
    (fun n => le_trans (norm_clusterTerm_le P n) (hb n))

/-- **Quantitative bound on the cluster sum.**  Under the same geometric weight
bound, `‖clusterSum P‖ ≤ C/(1−r)` — the explicit convergence estimate the KP
theorem delivers, now stated for the concrete Mayer object. -/
theorem norm_clusterSum_le [Fintype P.Polymer] (C r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hb : ∀ n, clusterWeight P n ≤ C * r ^ n) :
    ‖clusterSum P‖ ≤ C / (1 - r) := by
  have hnorms : Summable (fun n : ℕ => ‖(((n + 1).factorial : ℂ))⁻¹ *
      ∑ X : Fin (n + 1) → P.Polymer,
        (ursell P X : ℂ) * ∏ i, P.activity (X i)‖) :=
    cluster_series_summable _ C r hr0 hr1 (fun n => norm_nonneg _)
      (fun n => le_trans (norm_clusterTerm_le P n) (hb n))
  unfold clusterSum
  refine le_trans (norm_tsum_le_tsum_norm hnorms) ?_
  exact cluster_sum_le _ C r hr0 hr1 (fun n => norm_nonneg _)
    (fun n => le_trans (norm_clusterTerm_le P n) (hb n))

end YangMills.KP
