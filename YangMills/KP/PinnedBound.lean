/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.KP.KPBound
import YangMills.KP.PinnedCluster
import YangMills.KP.PinnedWalk

/-!
# Sharp KP, step 3 — the pinned per-size bound and the pinned cluster series

`docs/SHARP-KP-PLAN.md` §5, next brick: mirror the `kp_per_size_bound`
assembly with the 0-th polymer pinned, consuming `tree_walk_bound_pinned`
instead of the free walk bound.  The extensive factor `∑‖z‖` disappears,
replaced by the single activity `‖z(c)‖`:

* `tree_assignment_sum_le_pinned` — per-tree assignment sum over the root
  fiber `X 0 = c`, bounded by `Aᵐ` alone;
* `kp_pinned_per_size_bound` — `pinnedClusterWeight P c n ≤ ‖z c‖·(e·A)ⁿ`;
* `pinned_cluster_series_summable` / `pinned_cluster_tsum_le` — **the
  pinned KP bound**: `∑_n pinnedClusterWeight P c n ≤ ‖z c‖/(1 − e·A)`
  for `e·A < 1` — a *per-polymer* bound, the quantity that survives the
  infinite-volume limit.

Honest caveat: these still pass through the uniform majorant `a ≤ A`
(`A = t·#P` for the lattice gas).  The campaign's remaining step (shell
decomposition, plan §2 Route A) replaces `Aⁿ` by criterion-driven weights.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.KP

open SimpleGraph

open Classical in
/-- **Pinned per-tree assignment sum:** with the root polymer fixed, the
compatibility-weighted assignment sum over the remaining coordinates is
bounded by `Aᵐ` — no extensive factor. -/
lemma tree_assignment_sum_le_pinned (P : PolymerSystem) [Fintype P.Polymer]
    {a : P.Polymer → ℝ} (h : KPCriterion P a) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ x, a x ≤ A) {m : ℕ} {T : Finset (Sym2 (Fin (m + 1)))}
    (hT : T ∈ spanningTrees (⊤ : SimpleGraph (Fin (m + 1)))) (c : P.Polymer) :
    ∑ X ∈ (Finset.univ : Finset (Fin (m + 1) → P.Polymer)).filter
      (fun X => X 0 = c),
      (∏ e ∈ T, if e ∈ (incompGraph P X).edgeSet then (1 : ℝ) else 0)
        * ∏ v ∈ Finset.univ.filter (fun v : Fin (m + 1) => v ≠ 0),
            ‖P.activity (X v)‖
      ≤ A ^ m := by
  classical
  have htree := isTree_of_mem_spanningTrees _ hT
  have hconn := htree.isConnected
  -- pointwise conversion to the walk's parent-indexed shape (no root factor)
  have hpoint : ∀ X : Fin (m + 1) → P.Polymer,
      (∏ e ∈ T, if e ∈ (incompGraph P X).edgeSet then (1 : ℝ) else 0)
        * ∏ v ∈ Finset.univ.filter (fun v : Fin (m + 1) => v ≠ 0),
            ‖P.activity (X v)‖
      = ∏ v ∈ Finset.univ.filter (fun v : Fin (m + 1) => v ≠ 0),
          (if P.incomp (X (bfsParent T v)) (X v) then (1 : ℝ) else 0)
            * ‖P.activity (X v)‖ := by
    intro X
    rw [prod_tree_eq_prod_parents hT
      (fun e => if e ∈ (incompGraph P X).edgeSet then (1 : ℝ) else 0)]
    have hfac : ∀ v ∈ Finset.univ.filter (fun v : Fin (m + 1) => v ≠ 0),
        (if s(bfsParent T v, v) ∈ (incompGraph P X).edgeSet
          then (1 : ℝ) else 0)
        = if P.incomp (X (bfsParent T v)) (X v) then (1 : ℝ) else 0 := by
      intro v hv
      rw [Finset.mem_filter] at hv
      have hne : bfsParent T v ≠ v := by
        have hspec := (bfsParent_spec hconn hv.2).2
        intro hEq
        rw [hEq] at hspec
        omega
      simp [SimpleGraph.mem_edgeSet, incompGraph_adj, hne]
    rw [Finset.prod_congr rfl hfac, ← Finset.prod_mul_distrib]
  refine le_trans (le_of_eq (Finset.sum_congr rfl (fun X _ => hpoint X))) ?_
  -- the pinned walk bound
  refine tree_walk_bound_pinned m (Fin (m + 1)) P.Polymer 0 (bfsParent T)
    (bfsLevel T) (fun x y => if P.incomp x y then (1 : ℝ) else 0)
    (fun y => ‖P.activity y‖) A (by simp) ?_ ?_ ?_ hA0 ?_ c
  · -- descent
    intro v hv
    have hspec := (bfsParent_spec hconn hv).2
    omega
  · -- indicator nonneg
    intro x y
    dsimp only
    split_ifs <;> norm_num
  · -- weights nonneg
    intro y
    exact norm_nonneg _
  · -- the conditional neighbour bound = KP
    intro x
    dsimp only
    have h1 : ∑ y, (if P.incomp x y then (1 : ℝ) else 0) * ‖P.activity y‖
        = ∑ y ∈ Finset.univ.filter (fun y => P.incomp x y),
            ‖P.activity y‖ := by
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl (fun y _ => boole_mul _ _)
    rw [h1]
    exact le_trans (kp_neighbor_sum_le P h x) (hA x)

open Classical in
/-- **The pinned KP per-size bound:** the pinned cluster weight decays
geometrically with the *single* activity `‖z(c)‖` in front —
`pinnedClusterWeight P c n ≤ ‖z(c)‖·(e·A)ⁿ`.  Mirror of
`kp_per_size_bound` through the pinned walk. -/
theorem kp_pinned_per_size_bound (P : PolymerSystem) [Fintype P.Polymer]
    {a : P.Polymer → ℝ} (h : KPCriterion P a) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ x, a x ≤ A) (c : P.Polymer) (n : ℕ) :
    pinnedClusterWeight P c n
      ≤ ‖P.activity c‖ * (Real.exp 1 * A) ^ n := by
  classical
  set Sh : Finset (Finset (Sym2 (Fin (n + 1)))) :=
    (Finset.univ).filter (fun T : Finset (Sym2 (Fin (n + 1))) =>
      (fromEdgeSet (↑T : Set (Sym2 (Fin (n + 1))))).IsTree ∧
        ∀ e ∈ T, ¬ e.IsDiag) with hShdef
  have hsub : ∀ X : Fin (n + 1) → P.Polymer,
      spanningTrees (incompGraph P X) ⊆ Sh := by
    intro X T hT
    rw [hShdef, Finset.mem_filter]
    refine ⟨Finset.mem_univ T, isTree_of_mem_spanningTrees _ hT, ?_⟩
    intro e he
    have hmem := spanningTrees_subset _ hT he
    rw [SimpleGraph.mem_edgeFinset] at hmem
    exact (incompGraph P X).not_isDiag_of_mem_edgeSet hmem
  have hone : ∀ (X : Fin (n + 1) → P.Polymer)
      (T : Finset (Sym2 (Fin (n + 1)))),
      T ∈ spanningTrees (incompGraph P X) →
      (∏ e ∈ T, if e ∈ (incompGraph P X).edgeSet then (1 : ℝ) else 0)
        = 1 := by
    intro X T hT
    refine Finset.prod_eq_one fun e he => ?_
    have hmem := spanningTrees_subset _ hT he
    rw [SimpleGraph.mem_edgeFinset] at hmem
    rw [if_pos hmem]
  have hindnn : ∀ (X : Fin (n + 1) → P.Polymer)
      (T : Finset (Sym2 (Fin (n + 1)))),
      (0 : ℝ) ≤ ∏ e ∈ T,
        if e ∈ (incompGraph P X).edgeSet then (1 : ℝ) else 0 :=
    fun X T => Finset.prod_nonneg fun e _ => by split_ifs <;> norm_num
  have hpen : ∀ X : Fin (n + 1) → P.Polymer,
      |((ursell P X : ℤ) : ℝ)|
        ≤ ∑ T ∈ Sh, ∏ e ∈ T, if e ∈ (incompGraph P X).edgeSet
            then (1 : ℝ) else 0 := by
    intro X
    have h1 := abs_ursell_le_card_spanningTrees P X
    have h2 : |((ursell P X : ℤ) : ℝ)|
        ≤ ((spanningTrees (incompGraph P X)).card : ℝ) := by
      rw [← Int.cast_abs]
      exact_mod_cast h1
    refine le_trans h2 ?_
    have h3 : ((spanningTrees (incompGraph P X)).card : ℝ)
        = ∑ T ∈ spanningTrees (incompGraph P X),
            ∏ e ∈ T, if e ∈ (incompGraph P X).edgeSet
              then (1 : ℝ) else 0 := by
      rw [Finset.sum_congr rfl (fun T hT => hone X T hT)]
      simp
    rw [h3]
    exact Finset.sum_le_sum_of_subset_of_nonneg (hsub X)
      (fun T _ _ => hindnn X T)
  have htop : ∀ T ∈ Sh,
      T ∈ spanningTrees (⊤ : SimpleGraph (Fin (n + 1))) := by
    intro T hT
    rw [hShdef, Finset.mem_filter] at hT
    unfold spanningTrees
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨fun e he => ?_, hT.2.1⟩
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top,
      Set.mem_compl_iff, Sym2.mem_diagSet]
    exact hT.2.2 e he
  -- master pinned sum bound
  have hS : ∑ X ∈ (Finset.univ :
        Finset (Fin (n + 1) → P.Polymer)).filter (fun X => X 0 = c),
        |((ursell P X : ℤ) : ℝ)|
          * ∏ v ∈ Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0),
              ‖P.activity (X v)‖
      ≤ (Sh.card : ℝ) * A ^ n := by
    have hstep1 : ∑ X ∈ (Finset.univ :
          Finset (Fin (n + 1) → P.Polymer)).filter (fun X => X 0 = c),
          |((ursell P X : ℤ) : ℝ)|
            * ∏ v ∈ Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0),
                ‖P.activity (X v)‖
        ≤ ∑ X ∈ (Finset.univ :
            Finset (Fin (n + 1) → P.Polymer)).filter (fun X => X 0 = c),
            (∑ T ∈ Sh, ∏ e ∈ T, if e ∈ (incompGraph P X).edgeSet
                then (1 : ℝ) else 0)
              * ∏ v ∈ Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0),
                  ‖P.activity (X v)‖ := by
      refine Finset.sum_le_sum fun X _ => ?_
      exact mul_le_mul_of_nonneg_right (hpen X)
        (Finset.prod_nonneg fun v _ => norm_nonneg _)
    refine le_trans hstep1 ?_
    have hstep2 : ∑ X ∈ (Finset.univ :
          Finset (Fin (n + 1) → P.Polymer)).filter (fun X => X 0 = c),
          (∑ T ∈ Sh, ∏ e ∈ T, if e ∈ (incompGraph P X).edgeSet
              then (1 : ℝ) else 0)
            * ∏ v ∈ Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0),
                ‖P.activity (X v)‖
        = ∑ T ∈ Sh, ∑ X ∈ (Finset.univ :
            Finset (Fin (n + 1) → P.Polymer)).filter (fun X => X 0 = c),
            (∏ e ∈ T, if e ∈ (incompGraph P X).edgeSet then (1 : ℝ) else 0)
              * ∏ v ∈ Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0),
                  ‖P.activity (X v)‖ := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun X _ => by rw [Finset.sum_mul]
    rw [hstep2]
    have hstep3 : ∑ T ∈ Sh, ∑ X ∈ (Finset.univ :
          Finset (Fin (n + 1) → P.Polymer)).filter (fun X => X 0 = c),
          (∏ e ∈ T, if e ∈ (incompGraph P X).edgeSet then (1 : ℝ) else 0)
            * ∏ v ∈ Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0),
                ‖P.activity (X v)‖
        ≤ ∑ _T ∈ Sh, A ^ n :=
      Finset.sum_le_sum fun T hT =>
        tree_assignment_sum_le_pinned P h hA0 hA (htop T hT) c
    refine le_trans hstep3 ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  -- counting and the factorial absorption (verbatim from the free case)
  have hcount : (Sh.card : ℝ) ≤ ((n + 1 : ℕ) ^ (n + 1) : ℕ) := by
    have h1 := treeCount_le_pow n
    have h2 : Sh.card = treeCount (n + 1) := by
      rw [hShdef]
      rfl
    rw [h2]
    exact_mod_cast h1
  have hkey : (((n + 1 : ℕ) ^ (n + 1) : ℕ) : ℝ)
      ≤ Real.exp 1 ^ n * ((n + 1).factorial : ℝ) := by
    have hsucc := succ_pow_le_exp_mul_factorial n
    have hexp : Real.exp 1 ^ n = Real.exp n := by
      rw [← Real.exp_nat_mul, mul_one]
    calc (((n + 1 : ℕ) ^ (n + 1) : ℕ) : ℝ)
        = ((n : ℝ) + 1) ^ n * ((n : ℝ) + 1) := by push_cast; ring
      _ ≤ (Real.exp n * (n.factorial : ℝ)) * ((n : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right hsucc (by positivity)
      _ = Real.exp 1 ^ n * ((n + 1).factorial : ℝ) := by
          rw [hexp, Nat.factorial_succ]
          push_cast
          ring
  -- factor the pinned activity out of the inner products and assemble
  have hfactor : ∀ X ∈ (Finset.univ :
      Finset (Fin (n + 1) → P.Polymer)).filter (fun X => X 0 = c),
      |((ursell P X : ℤ) : ℝ)| * ∏ i, ‖P.activity (X i)‖
      = ‖P.activity c‖ * (|((ursell P X : ℤ) : ℝ)|
          * ∏ v ∈ Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0),
              ‖P.activity (X v)‖) := by
    intro X hX
    rw [Finset.mem_filter] at hX
    have hsplit : ∏ i, ‖P.activity (X i)‖
        = (∏ v ∈ Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0),
            ‖P.activity (X v)‖) * ‖P.activity (X 0)‖ := by
      rw [Finset.filter_ne',
        ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ 0)]
      ring
    rw [hsplit, hX.2]
    ring
  unfold pinnedClusterWeight
  rw [Finset.sum_congr rfl hfactor, ← Finset.mul_sum]
  calc (((n + 1).factorial : ℝ))⁻¹ * (‖P.activity c‖ *
        ∑ X ∈ (Finset.univ :
          Finset (Fin (n + 1) → P.Polymer)).filter (fun X => X 0 = c),
          |((ursell P X : ℤ) : ℝ)|
            * ∏ v ∈ Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0),
                ‖P.activity (X v)‖)
      ≤ (((n + 1).factorial : ℝ))⁻¹ * (‖P.activity c‖ *
          ((Sh.card : ℝ) * A ^ n)) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hS (norm_nonneg _)) (by positivity)
    _ ≤ (((n + 1).factorial : ℝ))⁻¹ * (‖P.activity c‖ *
          ((Real.exp 1 ^ n * ((n + 1).factorial : ℝ)) * A ^ n)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (le_trans hcount hkey)
            (pow_nonneg hA0 n)) (norm_nonneg _)) (by positivity)
    _ = ‖P.activity c‖ * (Real.exp 1 * A) ^ n := by
        rw [mul_pow]
        field_simp

/-- **The pinned cluster series converges** under the KP smallness `e·A < 1`. -/
theorem pinned_cluster_series_summable (P : PolymerSystem) [Fintype P.Polymer]
    {a : P.Polymer → ℝ} (h : KPCriterion P a) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ x, a x ≤ A) (hr : Real.exp 1 * A < 1) (c : P.Polymer) :
    Summable (fun n => pinnedClusterWeight P c n) :=
  Summable.of_nonneg_of_le (fun n => pinnedClusterWeight_nonneg P c n)
    (fun n => kp_pinned_per_size_bound P h hA0 hA c n)
    ((summable_geometric_of_lt_one (by positivity) hr).mul_left
      ‖P.activity c‖)

/-- **THE PINNED KP BOUND (uniform-A form):** the total pinned cluster
weight at a polymer `c` is at most `‖z(c)‖/(1 − e·A)` — a **per-polymer**
bound, the quantity that survives the infinite-volume limit (the total
cluster sum is extensive; this is not). -/
theorem pinned_cluster_tsum_le (P : PolymerSystem) [Fintype P.Polymer]
    {a : P.Polymer → ℝ} (h : KPCriterion P a) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ x, a x ≤ A) (hr : Real.exp 1 * A < 1) (c : P.Polymer) :
    ∑' n, pinnedClusterWeight P c n
      ≤ ‖P.activity c‖ / (1 - Real.exp 1 * A) := by
  have hgeom : Summable (fun n => ‖P.activity c‖ * (Real.exp 1 * A) ^ n) :=
    (summable_geometric_of_lt_one (by positivity) hr).mul_left _
  calc ∑' n, pinnedClusterWeight P c n
      ≤ ∑' n, ‖P.activity c‖ * (Real.exp 1 * A) ^ n :=
        (pinned_cluster_series_summable P h hA0 hA hr c).tsum_le_tsum
          (fun n => kp_pinned_per_size_bound P h hA0 hA c n) hgeom
    _ = ‖P.activity c‖ * (1 - Real.exp 1 * A)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hr]
    _ = ‖P.activity c‖ / (1 - Real.exp 1 * A) := by
        rw [div_eq_mul_inv]

end YangMills.KP
