/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.KP.ClusterWeight

/-!
# Sharp KP, step 1 — pinned cluster weights

Anchor of the sharp-KP campaign (`docs/SHARP-KP-PLAN.md`, Route A).  The
sharp Kotecký–Preiss estimate is a statement about clusters **pinned at a
polymer**: under the KP criterion alone (no uniform majorant of the
weights), the pinned weighted sum is finite per polymer — the form that
survives the infinite-volume limit, since the *total* cluster sum is
extensive and cannot be volume-uniform.

This file provides the object and its exact relation to the total weight:

* `pinnedClusterWeight P c n` — the contribution of size-`(n+1)` tuples
  whose 0-th coordinate is `c`;
* `pinnedClusterWeight_nonneg`;
* `clusterWeight_eq_sum_pinned` — **exact pinning decomposition**:
  `clusterWeight P n = ∑_c pinnedClusterWeight P c n` (fiberwise over the
  0-th coordinate; no overcounting, since pinning is at a fixed coordinate
  rather than by membership);
* `pinnedClusterWeight_le_clusterWeight` — each pin is dominated by the
  total.

The campaign's target (`kp_pinned_cluster_bound`, see the plan) bounds
`∑_n pinnedClusterWeight`-type sums by `e^{a(c)} − 1` under `KPCriterion`.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.KP

open scoped BigOperators

variable (P : PolymerSystem)

open Classical in
/-- The **pinned cluster weight**: the part of `clusterWeight P n` carried
by tuples whose 0-th polymer is `c`. -/
noncomputable def pinnedClusterWeight [Fintype P.Polymer]
    (c : P.Polymer) (n : ℕ) : ℝ :=
  (((n + 1).factorial : ℝ))⁻¹ *
    ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → P.Polymer)).filter
      (fun X => X 0 = c),
      |((ursell P X : ℤ) : ℝ)| * ∏ i, ‖P.activity (X i)‖

open Classical in
lemma pinnedClusterWeight_nonneg [Fintype P.Polymer]
    (c : P.Polymer) (n : ℕ) :
    0 ≤ pinnedClusterWeight P c n := by
  unfold pinnedClusterWeight
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun X _ => ?_)
  exact mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)

open Classical in
/-- **The pinning decomposition** — exact, with no overcounting: the total
per-size weight is the sum of the weights pinned at each polymer (fiberwise
over the 0-th coordinate). -/
theorem clusterWeight_eq_sum_pinned [Fintype P.Polymer] (n : ℕ) :
    clusterWeight P n = ∑ c : P.Polymer, pinnedClusterWeight P c n := by
  unfold clusterWeight pinnedClusterWeight
  rw [← Finset.mul_sum]
  congr 1
  exact (Finset.sum_fiberwise_of_maps_to
    (fun X _ => Finset.mem_univ (X 0)) _).symm

open Classical in
/-- Each pinned weight is dominated by the total per-size weight. -/
theorem pinnedClusterWeight_le_clusterWeight [Fintype P.Polymer]
    (c : P.Polymer) (n : ℕ) :
    pinnedClusterWeight P c n ≤ clusterWeight P n := by
  rw [clusterWeight_eq_sum_pinned]
  exact Finset.single_le_sum
    (fun c' _ => pinnedClusterWeight_nonneg P c' n) (Finset.mem_univ c)

end YangMills.KP
