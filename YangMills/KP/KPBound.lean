/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.KP.Criterion
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

end YangMills.KP
