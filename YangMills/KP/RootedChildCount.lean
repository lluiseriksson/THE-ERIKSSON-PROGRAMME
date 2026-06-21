/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.KP.PenroseFiber

/-!
# Rooted child counts for Penrose/BFS trees

This module exposes the finite rooted-tree bookkeeping needed by the
degree-sensitive Appendix-F leaf summation.  The existing Penrose/BFS API
already orients a spanning tree on `Fin (n+1)` away from the root `0` through
`bfsParent`; here we name the children of a vertex and prove that the total
number of children over all vertices is exactly the number of nonroot vertices.

No analytic KP estimate, source theorem, or Yang-Mills claim is introduced.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.KP

open SimpleGraph
open scoped BigOperators

variable {n : ℕ}

/-- Children of `v` in the root-`0` BFS orientation of an edge set `T`.
Only nonroot vertices are assigned to a parent. -/
noncomputable def rootedChildren
    (T : Finset (Sym2 (Fin (n + 1)))) (v : Fin (n + 1)) :
    Finset (Fin (n + 1)) :=
  (Finset.univ : Finset (Fin (n + 1))).filter
    (fun w => w ≠ 0 ∧ bfsParent T w = v)

/-- Number of root-`0` BFS children of a vertex. -/
noncomputable def rootedChildCount
    (T : Finset (Sym2 (Fin (n + 1)))) (v : Fin (n + 1)) : ℕ :=
  (rootedChildren T v).card

/-- Independent child-order choices for every rooted BFS child fiber of `T`.
This is the finite assignment object whose cardinality is the product of the
child-factorials used in the Appendix-F leaf bookkeeping. -/
abbrev rootedChildOrderAssignments
    (T : Finset (Sym2 (Fin (n + 1)))) : Type :=
  ∀ v : Fin (n + 1), Equiv.Perm {w : Fin (n + 1) // w ∈ rootedChildren T v}

@[simp] theorem mem_rootedChildren
    (T : Finset (Sym2 (Fin (n + 1)))) (v w : Fin (n + 1)) :
    w ∈ rootedChildren T v ↔ w ≠ 0 ∧ bfsParent T w = v := by
  classical
  simp [rootedChildren]

/-- The number of independent child-order assignments is exactly the product
of the rooted child-factorials. -/
theorem card_rootedChildOrderAssignments
    (T : Finset (Sym2 (Fin (n + 1)))) :
    Fintype.card (rootedChildOrderAssignments T) =
      ∏ v : Fin (n + 1), (rootedChildCount T v).factorial := by
  classical
  have hcard :
      ∀ v : Fin (n + 1),
        Fintype.card {w : Fin (n + 1) // w ∈ rootedChildren T v} =
          rootedChildCount T v := by
    intro v
    simpa [rootedChildCount] using Fintype.card_coe (rootedChildren T v)
  change
    Fintype.card
        (∀ v : Fin (n + 1),
          Equiv.Perm {w : Fin (n + 1) // w ∈ rootedChildren T v}) =
      ∏ v : Fin (n + 1), (rootedChildCount T v).factorial
  rw [Fintype.card_pi]
  exact Finset.prod_congr rfl fun v _hv => by
    rw [Fintype.card_perm, hcard v]

theorem rootedChild_ne_zero
    {T : Finset (Sym2 (Fin (n + 1)))} {v w : Fin (n + 1)}
    (hw : w ∈ rootedChildren T v) : w ≠ 0 :=
  (mem_rootedChildren T v w).mp hw |>.1

theorem rootedChild_parent_eq
    {T : Finset (Sym2 (Fin (n + 1)))} {v w : Fin (n + 1)}
    (hw : w ∈ rootedChildren T v) : bfsParent T w = v :=
  (mem_rootedChildren T v w).mp hw |>.2

/-- Every nonroot vertex lies in the child fiber of its BFS parent. -/
theorem mem_rootedChildren_parent
    (T : Finset (Sym2 (Fin (n + 1)))) {w : Fin (n + 1)}
    (hw : w ≠ 0) : w ∈ rootedChildren T (bfsParent T w) := by
  classical
  simp [rootedChildren, hw]

/-- The BFS child fiber is unique: a vertex cannot be a child of two
different parents. -/
theorem rootedChild_parent_unique
    {T : Finset (Sym2 (Fin (n + 1)))} {u v w : Fin (n + 1)}
    (hu : w ∈ rootedChildren T u) (hv : w ∈ rootedChildren T v) :
    u = v :=
  (rootedChild_parent_eq hu).symm.trans (rootedChild_parent_eq hv)

/-- Distinct parent fibers of the rooted child partition are disjoint. -/
theorem disjoint_rootedChildren_of_ne
    {T : Finset (Sym2 (Fin (n + 1)))} {u v : Fin (n + 1)}
    (huv : u ≠ v) : Disjoint (rootedChildren T u) (rootedChildren T v) := by
  classical
  rw [Finset.disjoint_left]
  intro w hwu hwv
  exact huv (rootedChild_parent_unique hwu hwv)

/-- The rooted child fibers cover exactly the nonroot vertices. -/
theorem biUnion_rootedChildren_eq_nonroot
    (T : Finset (Sym2 (Fin (n + 1)))) :
    (Finset.univ : Finset (Fin (n + 1))).biUnion (rootedChildren T) =
      (Finset.univ : Finset (Fin (n + 1))).filter (fun w => w ≠ 0) := by
  classical
  ext w
  constructor
  · intro hw
    rw [Finset.mem_biUnion] at hw
    rcases hw with ⟨v, _hv, hwv⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, rootedChild_ne_zero hwv⟩
  · intro hw
    have hw0 : w ≠ 0 := (Finset.mem_filter.mp hw).2
    rw [Finset.mem_biUnion]
    exact ⟨bfsParent T w, Finset.mem_univ _, mem_rootedChildren_parent T hw0⟩

/-- For a genuine spanning tree, every named child has its parent edge in the
tree edge set. -/
theorem rootedChild_parent_edge_mem {H : SimpleGraph (Fin (n + 1))}
    [Fintype H.edgeSet] {T : Finset (Sym2 (Fin (n + 1)))}
    (hT : T ∈ spanningTrees H) {v w : Fin (n + 1)}
    (hw : w ∈ rootedChildren T v) :
    s(v, w) ∈ T := by
  classical
  have hconn := (isTree_of_mem_spanningTrees H hT).isConnected
  have hw0 : w ≠ 0 := rootedChild_ne_zero hw
  have hparent : bfsParent T w = v := rootedChild_parent_eq hw
  have hadj := (bfsParent_spec hconn hw0).1
  rw [SimpleGraph.fromEdgeSet_adj] at hadj
  have hmem : s(bfsParent T w, w) ∈ T := Finset.mem_coe.mp hadj.1
  simpa [hparent] using hmem

/-- The children of all vertices partition the nonroot vertices.  In
particular, the sum of child counts is `n` for a tree on `n+1` labelled
vertices.  This is pure finite bookkeeping and does not require connectedness:
the parent map is a total function, and every nonroot vertex lies in exactly
one parent fiber. -/
theorem sum_rootedChildCount_eq
    (T : Finset (Sym2 (Fin (n + 1)))) :
    (∑ v : Fin (n + 1), rootedChildCount T v) = n := by
  classical
  let nonroot : Finset (Fin (n + 1)) :=
    (Finset.univ : Finset (Fin (n + 1))).filter (fun w => w ≠ 0)
  have hmaps :
      Set.MapsTo (fun w : Fin (n + 1) => bfsParent T w)
        ↑nonroot ↑(Finset.univ : Finset (Fin (n + 1))) := by
    intro w _hw
    exact Finset.mem_univ _
  have hfiber :
      nonroot.card =
        ∑ v ∈ (Finset.univ : Finset (Fin (n + 1))),
          (nonroot.filter (fun w => bfsParent T w = v)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hfilter :
      ∀ v : Fin (n + 1),
        (nonroot.filter (fun w => bfsParent T w = v)) =
          (Finset.univ : Finset (Fin (n + 1))).filter
            (fun w => w ≠ 0 ∧ bfsParent T w = v) := by
    intro v
    ext w
    simp [nonroot]
  have hsum :
      (∑ v : Fin (n + 1), rootedChildCount T v) = nonroot.card := by
    rw [hfiber]
    simp [rootedChildCount, rootedChildren, hfilter]
  calc
    (∑ v : Fin (n + 1), rootedChildCount T v) = nonroot.card := hsum
    _ = n := by
      change (((Finset.univ : Finset (Fin (n + 1))).filter
        (fun w => w ≠ 0)).card) = n
      rw [Finset.filter_ne',
        Finset.card_erase_of_mem (Finset.mem_univ (0 : Fin (n + 1))),
        Finset.card_univ, Fintype.card_fin]
      omega

/-- Grouping a parent-indexed product by BFS child fibers.  Every nonroot
vertex contributes one factor evaluated at its parent; regrouping by parent
turns this into the product over vertices of that factor raised to the rooted
child count. -/
theorem prod_bfsParent_nonroot_eq_prod_pow_rootedChildCount
    {M : Type*} [CommMonoid M]
    (T : Finset (Sym2 (Fin (n + 1)))) (f : Fin (n + 1) → M) :
    (∏ w ∈ (Finset.univ : Finset (Fin (n + 1))).filter (fun w => w ≠ 0),
      f (bfsParent T w)) =
      ∏ v : Fin (n + 1), f v ^ rootedChildCount T v := by
  classical
  let nonroot : Finset (Fin (n + 1)) :=
    (Finset.univ : Finset (Fin (n + 1))).filter (fun w => w ≠ 0)
  have hmaps :
      Set.MapsTo (fun w : Fin (n + 1) => bfsParent T w)
        ↑nonroot ↑(Finset.univ : Finset (Fin (n + 1))) := by
    intro w _hw
    exact Finset.mem_univ _
  have hfilter :
      ∀ v : Fin (n + 1),
        nonroot.filter (fun w => bfsParent T w = v) = rootedChildren T v := by
    intro v
    ext w
    simp [nonroot, rootedChildren]
  calc
    (∏ w ∈ (Finset.univ : Finset (Fin (n + 1))).filter (fun w => w ≠ 0),
      f (bfsParent T w))
        = ∏ w ∈ nonroot, f (bfsParent T w) := by rfl
    _ =
        ∏ v ∈ (Finset.univ : Finset (Fin (n + 1))),
          ∏ w ∈ nonroot.filter (fun w => bfsParent T w = v),
            f (bfsParent T w) := by
          rw [← Finset.prod_fiberwise_of_maps_to hmaps
            (fun w => f (bfsParent T w))]
    _ =
        ∏ v ∈ (Finset.univ : Finset (Fin (n + 1))),
          ∏ _w ∈ nonroot.filter (fun w => bfsParent T w = v), f v := by
          refine Finset.prod_congr rfl fun v _hv => ?_
          refine Finset.prod_congr rfl fun w hw => ?_
          rw [(Finset.mem_filter.mp hw).2]
    _ =
        ∏ v ∈ (Finset.univ : Finset (Fin (n + 1))),
          f v ^ rootedChildCount T v := by
          refine Finset.prod_congr rfl fun v _hv => ?_
          rw [hfilter v, Finset.prod_const, rootedChildCount]
    _ = ∏ v : Fin (n + 1), f v ^ rootedChildCount T v := by
          rfl

/-- A finite factorial product divides the factorial of the total sum.  This
is the reusable multinomial bookkeeping lemma needed when independent child
orders are priced by parent fibers. -/
theorem prod_factorial_dvd_factorial_sum {α : Type*} [DecidableEq α]
    (s : Finset α) (m : α → ℕ) :
    (∏ i ∈ s, (m i).factorial) ∣ (∑ i ∈ s, m i).factorial := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih
    have hbin : (∑ i ∈ s, m i).factorial * (m a).factorial ∣
        ((∑ i ∈ s, m i) + m a).factorial :=
      Nat.factorial_mul_factorial_dvd_factorial_add _ _
    have hmul : (∏ i ∈ s, (m i).factorial) * (m a).factorial ∣
        (∑ i ∈ s, m i).factorial * (m a).factorial :=
      Nat.mul_dvd_mul_right ih _
    have h := dvd_trans hmul hbin
    simpa [Finset.sum_insert, Finset.prod_insert, ha, Nat.add_comm,
      Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

/-- Inequality form of `prod_factorial_dvd_factorial_sum`. -/
theorem prod_factorial_le_factorial_sum {α : Type*} [DecidableEq α]
    (s : Finset α) (m : α → ℕ) :
    (∏ i ∈ s, (m i).factorial) ≤ (∑ i ∈ s, m i).factorial := by
  exact Nat.le_of_dvd (Nat.factorial_pos _)
    (prod_factorial_dvd_factorial_sum s m)

/-- The product of factorials of all rooted child counts divides `n!`. -/
theorem rootedChildCount_factorialProduct_dvd_factorial
    (T : Finset (Sym2 (Fin (n + 1)))) :
    (∏ v : Fin (n + 1), (rootedChildCount T v).factorial) ∣ n.factorial := by
  classical
  have h := prod_factorial_dvd_factorial_sum
    (Finset.univ : Finset (Fin (n + 1))) (fun v => rootedChildCount T v)
  simpa [sum_rootedChildCount_eq T] using h

/-- The product of factorials of all rooted child counts is bounded by `n!`.
This is the finite child-fiber price used by degree-sensitive leaf summation. -/
theorem rootedChildCount_factorialProduct_le_factorial
    (T : Finset (Sym2 (Fin (n + 1)))) :
    (∏ v : Fin (n + 1), (rootedChildCount T v).factorial) ≤ n.factorial := by
  exact Nat.le_of_dvd (Nat.factorial_pos n)
    (rootedChildCount_factorialProduct_dvd_factorial T)

/-- Real-cast form of the rooted child factorial product bound. -/
theorem rootedChildCount_factorialProduct_real_le_factorial
    (T : Finset (Sym2 (Fin (n + 1)))) :
    (∏ v : Fin (n + 1), ((rootedChildCount T v).factorial : ℝ)) ≤
      (n.factorial : ℝ) := by
  exact_mod_cast rootedChildCount_factorialProduct_le_factorial T

/-- After the second-Ursell `(n+1)!` normalization, independent child-order
factorials cost at most the single marked-root factor `(n+1)⁻¹`. -/
theorem rootedChildCount_factorialProduct_inv_succ_factorial_le_inv_succ
    (T : Finset (Sym2 (Fin (n + 1)))) :
    (((n + 1).factorial : ℝ))⁻¹ *
        (∏ v : Fin (n + 1), ((rootedChildCount T v).factorial : ℝ)) ≤
      (((n : ℝ) + 1)⁻¹) := by
  have hprod := rootedChildCount_factorialProduct_real_le_factorial T
  have hfacpos : 0 < (((n + 1).factorial : ℕ) : ℝ) := by positivity
  have hnfacpos : 0 < ((n.factorial : ℕ) : ℝ) := by positivity
  calc
    (((n + 1).factorial : ℝ))⁻¹ *
        (∏ v : Fin (n + 1), ((rootedChildCount T v).factorial : ℝ))
        ≤ (((n + 1).factorial : ℝ))⁻¹ * (n.factorial : ℝ) := by
          exact mul_le_mul_of_nonneg_left hprod (inv_nonneg.mpr hfacpos.le)
    _ = (((n : ℝ) + 1)⁻¹) := by
          rw [Nat.factorial_succ]
          push_cast
          field_simp [hnfacpos.ne']

end YangMills.KP
