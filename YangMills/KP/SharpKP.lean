/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.KP.SharpShell
import YangMills.KP.KPBound

/-!
# Sharp Kotecký–Preiss — the convergence corollaries

The endpoint of `docs/SHARP-KP-PLAN.md`: from the pinned bound
`kp_pinned_cluster_bound` (SharpShell), the Mayer cluster series of any
finite polymer system converges **under the bare KP criterion** — no
uniform majorant `A`, no `e·A < 1` smallness anywhere:

* `kp_clusterWeight_summable_sharp` — the per-size weights are summable;
* `kp_convergence_sharp` — absolute convergence of the cluster series;
* `kp_norm_clusterSum_le_sharp` —
  `‖clusterSum P‖ ≤ ∑_c ‖z(c)‖·e^{a(c)}`.

These replace `kp_convergence`/`kp_norm_clusterSum_le` (KPBound.lean),
whose `∀ x, a x ≤ A` + `e·A < 1` hypotheses were volume-dependent for
the lattice gas.  Composed with
`connectedLatticePolymerSystem_kpCriterion_volumeUniform`
(ConnectedEntropy.lean) they give volume-uniform convergence of the
connected lattice polymer gas.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.KP

open scoped BigOperators

open Classical in
/-- **Sharp summability of the per-size cluster weights** under the bare
KP criterion: sum the pinning decomposition over the (finitely many)
polymers. -/
theorem kp_clusterWeight_summable_sharp (P : PolymerSystem)
    [Fintype P.Polymer] {a : P.Polymer → ℝ} (h : KPCriterion P a) :
    Summable (fun n => clusterWeight P n) := by
  classical
  refine Summable.congr (f := fun n => ∑ c : P.Polymer,
    pinnedClusterWeight P c n) ?_ ?_
  · exact summable_sum fun c _ =>
      (pinned_cluster_summable_sharp P h c).1
  · exact fun n => (clusterWeight_eq_sum_pinned (P := P) n).symm

open Classical in
/-- **Sharp Kotecký–Preiss convergence:** the Mayer cluster series
converges absolutely under the bare KP criterion — no uniform majorant
of the weights, no geometric smallness hypothesis. -/
theorem kp_convergence_sharp (P : PolymerSystem) [Fintype P.Polymer]
    {a : P.Polymer → ℝ} (h : KPCriterion P a) :
    Summable (fun n : ℕ => (((n + 1).factorial : ℂ))⁻¹ *
      ∑ X : Fin (n + 1) → P.Polymer,
        (ursell P X : ℂ) * ∏ i, P.activity (X i)) := by
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => norm_clusterTerm_le P n) ?_
  exact kp_clusterWeight_summable_sharp P h

open Classical in
/-- **Sharp quantitative bound on the cluster sum:**
`‖clusterSum P‖ ≤ ∑_c ‖z(c)‖·e^{a(c)}` under the bare KP criterion —
every quantity finite and per-polymer. -/
theorem kp_norm_clusterSum_le_sharp (P : PolymerSystem)
    [Fintype P.Polymer] {a : P.Polymer → ℝ} (h : KPCriterion P a) :
    ‖clusterSum P‖
      ≤ ∑ c : P.Polymer, ‖P.activity c‖ * Real.exp (a c) := by
  classical
  have hnorms : Summable (fun n : ℕ =>
      ‖(((n + 1).factorial : ℂ))⁻¹ *
        ∑ X : Fin (n + 1) → P.Polymer,
          (ursell P X : ℂ) * ∏ i, P.activity (X i)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => norm_clusterTerm_le P n)
      (kp_clusterWeight_summable_sharp P h)
  unfold clusterSum
  refine le_trans (norm_tsum_le_tsum_norm hnorms) ?_
  calc ∑' n, ‖(((n + 1).factorial : ℂ))⁻¹ *
        ∑ X : Fin (n + 1) → P.Polymer,
          (ursell P X : ℂ) * ∏ i, P.activity (X i)‖
      ≤ ∑' n, clusterWeight P n :=
        Summable.tsum_le_tsum (fun n => norm_clusterTerm_le P n)
          hnorms (kp_clusterWeight_summable_sharp P h)
    _ = ∑' n, ∑ c : P.Polymer, pinnedClusterWeight P c n :=
        tsum_congr fun n => clusterWeight_eq_sum_pinned (P := P) n
    _ = ∑ c : P.Polymer, ∑' n, pinnedClusterWeight P c n :=
        Summable.tsum_finsetSum fun c _ =>
          (pinned_cluster_summable_sharp P h c).1
    _ ≤ ∑ c : P.Polymer, ‖P.activity c‖ * Real.exp (a c) :=
        Finset.sum_le_sum fun c _ =>
          (pinned_cluster_summable_sharp P h c).2

end YangMills.KP
