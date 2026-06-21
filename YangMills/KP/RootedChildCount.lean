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

@[simp] theorem mem_rootedChildren
    (T : Finset (Sym2 (Fin (n + 1)))) (v w : Fin (n + 1)) :
    w ∈ rootedChildren T v ↔ w ≠ 0 ∧ bfsParent T w = v := by
  classical
  simp [rootedChildren]

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

end YangMills.KP
