/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.KP.Criterion
import YangMills.KP.ClusterWeight
import YangMills.KP.PenroseFiber
import YangMills.KP.WalkBound

/-!
# T2 assembly — the per-tree assignment sum under the KP criterion

Bridges the abstract `tree_walk_bound` to the concrete polymer objects:
for a spanning tree `T` on `Fin (m+1)`, the sum over all polymer assignments
of (tree-compatibility indicator) × (activity weights) is at most
`Aᵐ · ∑‖z‖`, where `A` dominates the KP weight `a`.

The conversion: the compatibility indicator factorizes over the tree's edges
(`Finset.prod_boole`), tree-edge products are parent-indexed vertex products
(`prod_tree_eq_prod_parents`), each parent edge's membership in the
incompatibility graph is exactly the `incomp` relation (the endpoints differ
since parents sit one level down), and then `tree_walk_bound` applies with
the conditional neighbour bound supplied by `kp_neighbor_sum_le`.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.KP

open SimpleGraph

open Classical in
/-- **Per-tree assignment sum.**  For a spanning tree `T` of the complete
graph on `Fin (m+1)` and a polymer system satisfying the KP criterion with
weight dominated by `A`, the compatibility-weighted assignment sum obeys
`∑_X (∏_{e∈T} 𝟙[e ∈ incompEdges X]) · ∏ᵢ‖z(Xᵢ)‖ ≤ Aᵐ · ∑‖z‖`. -/
lemma tree_assignment_sum_le (P : PolymerSystem) [Fintype P.Polymer]
    {a : P.Polymer → ℝ} (h : KPCriterion P a) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ x, a x ≤ A) {m : ℕ} {T : Finset (Sym2 (Fin (m + 1)))}
    (hT : T ∈ spanningTrees (⊤ : SimpleGraph (Fin (m + 1)))) :
    ∑ X : Fin (m + 1) → P.Polymer,
      (∏ e ∈ T, if e ∈ (incompGraph P X).edgeSet then (1 : ℝ) else 0)
        * ∏ i, ‖P.activity (X i)‖
      ≤ A ^ m * ∑ y, ‖P.activity y‖ := by
  classical
  have htree := isTree_of_mem_spanningTrees _ hT
  have hconn := htree.isConnected
  -- pointwise conversion to the walk's parent-indexed shape
  have hpoint : ∀ X : Fin (m + 1) → P.Polymer,
      (∏ e ∈ T, if e ∈ (incompGraph P X).edgeSet then (1 : ℝ) else 0)
        * ∏ i, ‖P.activity (X i)‖
      = (∏ v ∈ Finset.univ.filter (fun v : Fin (m + 1) => v ≠ 0),
          (if P.incomp (X (bfsParent T v)) (X v) then (1 : ℝ) else 0)
            * ‖P.activity (X v)‖) * ‖P.activity (X 0)‖ := by
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
    rw [Finset.prod_congr rfl hfac]
    have hsplit : ∏ i, ‖P.activity (X i)‖
        = (∏ v ∈ Finset.univ.filter (fun v : Fin (m + 1) => v ≠ 0),
            ‖P.activity (X v)‖) * ‖P.activity (X 0)‖ := by
      rw [Finset.filter_ne',
        ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ 0)]
      ring
    rw [hsplit, ← mul_assoc, ← Finset.prod_mul_distrib]
  refine le_trans (le_of_eq (Finset.sum_congr rfl (fun X _ => hpoint X))) ?_
  -- the abstract walk bound
  refine tree_walk_bound m (Fin (m + 1)) P.Polymer 0 (bfsParent T)
    (bfsLevel T) (fun x y => if P.incomp x y then (1 : ℝ) else 0)
    (fun y => ‖P.activity y‖) A (by simp) ?_ ?_ ?_ hA0 ?_
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

/-- **The Kotecký–Preiss per-size cluster bound (Target B's estimate).**
Under the KP criterion with weight dominated by `A ≥ 0`, the per-size
absolute cluster weight decays geometrically:
`clusterWeight P n ≤ (∑‖z‖) · (e·A)ⁿ`.

Assembly of the proved pieces: Penrose (`abs_ursell_le_card_spanningTrees`)
expands `|φ(X)|` into a sum of edge-compatibility products over universal
tree shapes; summing assignments per tree is `tree_assignment_sum_le`
(the walk); shapes are counted by `treeCount_le_pow`; and the factorial is
absorbed by `succ_pow_le_exp_mul_factorial`.  Feeding this into
`clusterSum_summable_of_geometric` / `norm_clusterSum_le` gives KP
convergence whenever `e·A < 1`. -/
theorem kp_per_size_bound (P : PolymerSystem) [Fintype P.Polymer]
    {a : P.Polymer → ℝ} (h : KPCriterion P a) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ x, a x ≤ A) (n : ℕ) :
    clusterWeight P n ≤ (∑ y, ‖P.activity y‖) * (Real.exp 1 * A) ^ n := by
  classical
  -- the universal tree shapes
  set Sh : Finset (Finset (Sym2 (Fin (n + 1)))) :=
    (Finset.univ).filter (fun T : Finset (Sym2 (Fin (n + 1))) =>
      (fromEdgeSet (↑T : Set (Sym2 (Fin (n + 1))))).IsTree ∧
        ∀ e ∈ T, ¬ e.IsDiag) with hShdef
  have hZnn : (0 : ℝ) ≤ ∑ y, ‖P.activity y‖ :=
    Finset.sum_nonneg fun y _ => norm_nonneg _
  have hAn : (0 : ℝ) ≤ A ^ n := pow_nonneg hA0 n
  -- every spanning tree of an incompatibility graph is a shape
  have hsub : ∀ X : Fin (n + 1) → P.Polymer,
      spanningTrees (incompGraph P X) ⊆ Sh := by
    intro X T hT
    rw [hShdef, Finset.mem_filter]
    refine ⟨Finset.mem_univ T, isTree_of_mem_spanningTrees _ hT, ?_⟩
    intro e he
    have hmem := spanningTrees_subset _ hT he
    rw [SimpleGraph.mem_edgeFinset] at hmem
    exact (incompGraph P X).not_isDiag_of_mem_edgeSet hmem
  -- on its own spanning trees, the compatibility product is 1
  have hone : ∀ (X : Fin (n + 1) → P.Polymer) (T : Finset (Sym2 (Fin (n + 1)))),
      T ∈ spanningTrees (incompGraph P X) →
      (∏ e ∈ T, if e ∈ (incompGraph P X).edgeSet then (1 : ℝ) else 0) = 1 := by
    intro X T hT
    refine Finset.prod_eq_one fun e he => ?_
    have hmem := spanningTrees_subset _ hT he
    rw [SimpleGraph.mem_edgeFinset] at hmem
    rw [if_pos hmem]
  have hindnn : ∀ (X : Fin (n + 1) → P.Polymer) (T : Finset (Sym2 (Fin (n + 1)))),
      (0 : ℝ) ≤ ∏ e ∈ T, if e ∈ (incompGraph P X).edgeSet then (1 : ℝ) else 0 :=
    fun X T => Finset.prod_nonneg fun e _ => by split_ifs <;> norm_num
  -- Penrose, expanded over shapes
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
            ∏ e ∈ T, if e ∈ (incompGraph P X).edgeSet then (1 : ℝ) else 0 := by
      rw [Finset.sum_congr rfl (fun T hT => hone X T hT)]
      simp
    rw [h3]
    exact Finset.sum_le_sum_of_subset_of_nonneg (hsub X)
      (fun T _ _ => hindnn X T)
  -- shapes are spanning trees of the complete graph
  have htop : ∀ T ∈ Sh, T ∈ spanningTrees (⊤ : SimpleGraph (Fin (n + 1))) := by
    intro T hT
    rw [hShdef, Finset.mem_filter] at hT
    unfold spanningTrees
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨fun e he => ?_, hT.2.1⟩
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top,
      Set.mem_compl_iff, Sym2.mem_diagSet]
    exact hT.2.2 e he
  -- master sum bound: Penrose expansion, swap, walk per tree
  have hS : ∑ X : Fin (n + 1) → P.Polymer,
        |((ursell P X : ℤ) : ℝ)| * ∏ i, ‖P.activity (X i)‖
      ≤ (Sh.card : ℝ) * (A ^ n * ∑ y, ‖P.activity y‖) := by
    have hstep1 : ∑ X : Fin (n + 1) → P.Polymer,
          |((ursell P X : ℤ) : ℝ)| * ∏ i, ‖P.activity (X i)‖
        ≤ ∑ X : Fin (n + 1) → P.Polymer,
            (∑ T ∈ Sh, ∏ e ∈ T, if e ∈ (incompGraph P X).edgeSet
                then (1 : ℝ) else 0) * ∏ i, ‖P.activity (X i)‖ := by
      refine Finset.sum_le_sum fun X _ => ?_
      exact mul_le_mul_of_nonneg_right (hpen X)
        (Finset.prod_nonneg fun i _ => norm_nonneg _)
    refine le_trans hstep1 ?_
    have hstep2 : ∑ X : Fin (n + 1) → P.Polymer,
          (∑ T ∈ Sh, ∏ e ∈ T, if e ∈ (incompGraph P X).edgeSet
              then (1 : ℝ) else 0) * ∏ i, ‖P.activity (X i)‖
        = ∑ T ∈ Sh, ∑ X : Fin (n + 1) → P.Polymer,
            (∏ e ∈ T, if e ∈ (incompGraph P X).edgeSet then (1 : ℝ) else 0)
              * ∏ i, ‖P.activity (X i)‖ := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun X _ => by rw [Finset.sum_mul]
    rw [hstep2]
    have hstep3 : ∑ T ∈ Sh, ∑ X : Fin (n + 1) → P.Polymer,
          (∏ e ∈ T, if e ∈ (incompGraph P X).edgeSet then (1 : ℝ) else 0)
            * ∏ i, ‖P.activity (X i)‖
        ≤ ∑ _T ∈ Sh, A ^ n * ∑ y, ‖P.activity y‖ :=
      Finset.sum_le_sum fun T hT =>
        tree_assignment_sum_le P h hA0 hA (htop T hT)
    refine le_trans hstep3 ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  -- counting and the factorial absorption
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
  -- assemble
  have hfacpos : (0 : ℝ) < ((n + 1).factorial : ℝ) := by positivity
  unfold clusterWeight
  calc (((n + 1).factorial : ℝ))⁻¹ *
        ∑ X : Fin (n + 1) → P.Polymer,
          |((ursell P X : ℤ) : ℝ)| * ∏ i, ‖P.activity (X i)‖
      ≤ (((n + 1).factorial : ℝ))⁻¹ *
          ((Sh.card : ℝ) * (A ^ n * ∑ y, ‖P.activity y‖)) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ ≤ (((n + 1).factorial : ℝ))⁻¹ *
          ((Real.exp 1 ^ n * ((n + 1).factorial : ℝ))
            * (A ^ n * ∑ y, ‖P.activity y‖)) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (le_trans hcount hkey)
            (by positivity)) (by positivity)
    _ = (∑ y, ‖P.activity y‖) * (Real.exp 1 * A) ^ n := by
        rw [mul_pow]
        field_simp

/-- **Kotecký–Preiss convergence (Target B, closed).**  Under the KP
criterion with weight uniformly dominated by `A` satisfying `e·A < 1`, the
series defining the cluster sum is absolutely summable. -/
theorem kp_convergence (P : PolymerSystem) [Fintype P.Polymer]
    {a : P.Polymer → ℝ} (h : KPCriterion P a) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ x, a x ≤ A) (hr : Real.exp 1 * A < 1) :
    Summable (fun n : ℕ => (((n + 1).factorial : ℂ))⁻¹ *
      ∑ X : Fin (n + 1) → P.Polymer,
        (ursell P X : ℂ) * ∏ i, P.activity (X i)) :=
  clusterSum_summable_of_geometric P (∑ y, ‖P.activity y‖) (Real.exp 1 * A)
    (by positivity) hr (kp_per_size_bound P h hA0 hA)

/-- **Quantitative KP bound on the cluster sum (Target B, closed):**
`‖clusterSum P‖ ≤ (∑‖z‖) / (1 − e·A)` whenever `e·A < 1`. -/
theorem kp_norm_clusterSum_le (P : PolymerSystem) [Fintype P.Polymer]
    {a : P.Polymer → ℝ} (h : KPCriterion P a) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ x, a x ≤ A) (hr : Real.exp 1 * A < 1) :
    ‖clusterSum P‖ ≤ (∑ y, ‖P.activity y‖) / (1 - Real.exp 1 * A) :=
  norm_clusterSum_le P (∑ y, ‖P.activity y‖) (Real.exp 1 * A)
    (by positivity) hr (kp_per_size_bound P h hA0 hA)

end YangMills.KP
