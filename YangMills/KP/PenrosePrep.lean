/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.KP.Cluster

/-!
# T2 (Penrose prep) — spanning trees, and the factorial–tree-count inequality

Groundwork for Target B's remaining open estimate
(`KPCriterion P a → clusterWeight P n ≤ C·rⁿ`, see `ClusterWeight.lean` and
`docs/HANDOFF-KP.md`).  Its proof route is:

  (i)   **Penrose tree-graph inequality** (open):
        `|ursell P X| ≤ (spanningTrees (incompGraph P X)).card` —
        the `spanningTrees` object is *defined* here so that inequality is
        now statable verbatim;
  (ii)  per-tree activity bound by walking tree edges with
        `kp_neighbor_sum_le` (open);
  (iii) Cayley-order tree counting: `#trees ≤ (n+1)^{n-1}` on `n+1` labeled
        vertices, compatible with the `1/(n+1)!` of `clusterWeight` because
        `(n+1)ⁿ ≤ eⁿ·n!` — **that analytic inequality is proved here**
        (`succ_pow_le_exp_mul_factorial`).  Crude `(n-1)`-subset counting of
        edge sets loses this bound and with it the geometric decay, which is
        why genuine tree counting is required.

No axiom is introduced; (i) and (ii) remain open lemmas, never assumed.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.KP

open SimpleGraph
open scoped BigOperators

/-- The **spanning trees** of a graph on `Fin n`: edge subsets `E` of `G`
whose `fromEdgeSet` is a tree on the full vertex set.  The Penrose tree-graph
inequality (Target B, step (i), open) is
`|ursell P X| ≤ (spanningTrees (incompGraph P X)).card`. -/
noncomputable def spanningTrees {n : ℕ} (G : SimpleGraph (Fin n))
    [Fintype G.edgeSet] : Finset (Finset (Sym2 (Fin n))) := by
  classical
  exact G.edgeFinset.powerset.filter
    (fun E => (fromEdgeSet (↑E : Set (Sym2 (Fin n)))).IsTree)

/-- Every spanning tree is a spanning subgraph supported on `G`'s edges. -/
lemma spanningTrees_subset {n : ℕ} (G : SimpleGraph (Fin n))
    [Fintype G.edgeSet] {E : Finset (Sym2 (Fin n))}
    (h : E ∈ spanningTrees G) : E ⊆ G.edgeFinset := by
  classical
  unfold spanningTrees at h
  simp only [Finset.mem_filter, Finset.mem_powerset] at h
  exact h.1

/-- A member of `spanningTrees G` is a tree as a spanning subgraph. -/
lemma isTree_of_mem_spanningTrees {n : ℕ} (G : SimpleGraph (Fin n))
    [Fintype G.edgeSet] {E : Finset (Sym2 (Fin n))}
    (h : E ∈ spanningTrees G) :
    (fromEdgeSet (↑E : Set (Sym2 (Fin n)))).IsTree := by
  classical
  unfold spanningTrees at h
  simp only [Finset.mem_filter, Finset.mem_powerset] at h
  exact h.2

/-- `1 + 1/(m+1) ≤ exp(1/(m+1))` — the seed of the `(1+1/k)^k ≤ e` bound. -/
private lemma one_add_inv_le_exp_inv (m : ℕ) :
    (1 : ℝ) + 1 / ((m : ℝ) + 1) ≤ Real.exp (1 / ((m : ℝ) + 1)) := by
  have h := Real.add_one_le_exp (1 / ((m : ℝ) + 1))
  linarith

/-- `((m+2)/(m+1))^(m+1) ≤ e` — the compound-interest bound `(1+1/k)^k ≤ e`. -/
private lemma ratio_pow_le_exp_one (m : ℕ) :
    (((m : ℝ) + 2) / ((m : ℝ) + 1)) ^ (m + 1) ≤ Real.exp 1 := by
  have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have heq : ((m : ℝ) + 2) / ((m : ℝ) + 1) = 1 + 1 / ((m : ℝ) + 1) := by
    field_simp
    ring
  rw [heq]
  have hbase : (0 : ℝ) ≤ 1 + 1 / ((m : ℝ) + 1) := by positivity
  calc (1 + 1 / ((m : ℝ) + 1)) ^ (m + 1)
      ≤ (Real.exp (1 / ((m : ℝ) + 1))) ^ (m + 1) := by
        gcongr
        exact one_add_inv_le_exp_inv m
    _ = Real.exp (((m : ℝ) + 1) * (1 / ((m : ℝ) + 1))) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
    _ = Real.exp 1 := by
        congr 1
        field_simp

/-- **Target B, step (iii): the factorial–tree-count inequality
`(n+1)ⁿ ≤ eⁿ·n!`.**  This is what makes a Cayley-order spanning-tree count
`≤ (n+1)^{n-1}` summable against the `1/(n+1)!` of `clusterWeight`:
`(n+1)^{n-1}/(n+1)! ≤ eⁿ/(n+1)`, a geometric factor.  Proved by induction from
the compound-interest bound `(1+1/k)^k ≤ e`. -/
theorem succ_pow_le_exp_mul_factorial (n : ℕ) :
    ((n : ℝ) + 1) ^ n ≤ Real.exp n * (n.factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ m ih =>
    push_cast
    have hkey : ((m : ℝ) + 1 + 1) ^ (m + 1)
        ≤ Real.exp 1 * ((m : ℝ) + 1) ^ (m + 1) := by
      have hratio := ratio_pow_le_exp_one m
      have hpow_pos : (0 : ℝ) < ((m : ℝ) + 1) ^ (m + 1) := by positivity
      have hexpand : ((m : ℝ) + 1 + 1) ^ (m + 1)
          = (((m : ℝ) + 2) / ((m : ℝ) + 1)) ^ (m + 1) * ((m : ℝ) + 1) ^ (m + 1) := by
        rw [← mul_pow]
        congr 1
        field_simp
        ring
      rw [hexpand]
      exact mul_le_mul_of_nonneg_right hratio hpow_pos.le
    have hstep : ((m : ℝ) + 1) ^ (m + 1)
        ≤ ((m : ℝ) + 1) * (Real.exp m * (m.factorial : ℝ)) := by
      rw [pow_succ, mul_comm (((m : ℝ) + 1) ^ m) ((m : ℝ) + 1)]
      exact mul_le_mul_of_nonneg_left ih (by positivity)
    calc ((m : ℝ) + 1 + 1) ^ (m + 1)
        ≤ Real.exp 1 * ((m : ℝ) + 1) ^ (m + 1) := hkey
      _ ≤ Real.exp 1 * (((m : ℝ) + 1) * (Real.exp m * (m.factorial : ℝ))) :=
          mul_le_mul_of_nonneg_left hstep (Real.exp_pos 1).le
      _ = Real.exp ((m : ℝ) + 1) * (((m + 1).factorial : ℝ)) := by
          rw [Real.exp_add, Nat.factorial_succ]
          push_cast
          ring

end YangMills.KP
