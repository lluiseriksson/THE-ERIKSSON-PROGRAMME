/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFSecondUrsellWeightedTree

/-!
# Appendix F: marked target vertices for the weighted second-Ursell tree term

This module proves a finite bookkeeping step needed before the weighted
second-Ursell tree majorant can be compared with pinned KP estimates.  If the
fixed target polymer contains an active skeleton point `r`, then every tuple in
the fixed-union fiber has at least one vertex whose active skeleton contains
`r`.  For nonnegative weights, the unmarked tree contribution is therefore
bounded by the same contribution with an inserted vertex marker.

No analytic leaf summation, CMP116 estimate, smallness condition, continuum
construction, or Clay conclusion is proved here.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

attribute [local instance] Classical.propDecidable

open Finset
open scoped BigOperators

namespace YangMills.RG

variable {d L : ℕ} [NeZero L]

/-- Coordinate-indexed target-skeleton marked weighted tree sum.  Compared
with `appendixFHoleHsharpWeightedTreeTerm`, this drops the fixed target-union
fiber and instead pins one coordinate by the event that its active skeleton
contains `r`. -/
noncomputable def appendixFHoleHsharpWeightedTreeMarkedIndexSum
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (r : Cube d L)
    (n : ℕ) : ℝ :=
  (((n + 1).factorial : ℝ))⁻¹ *
    ∑ i : Fin (n + 1),
      ∑ X ∈ (Finset.univ :
          Finset (Fin (n + 1) → OmegaPolymerType HF zK)).filter
            (fun X => r ∈ skeleton HF (X i).val),
        ∑ _T ∈ KP.spanningTrees
            (KP.incompGraph (omegaHolePolymerSystem HF zK) X),
          ∏ j, w (X j)

/-- Insert a target-skeleton marker into the weighted fixed-union `H#` tree
term.  The hypothesis `r ∈ skeleton HF Q.val` is the finite target marker: in
every tuple whose union is `Q.val`, `omegaClusterUnion_skeleton` forces some
vertex skeleton to contain `r`. -/
theorem appendixFHoleHsharpWeightedTreeTerm_le_markedSkeletonSum
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (Q : OmegaPolymerType HF zK)
    (r : Cube d L)
    (n : ℕ)
    (hw : ∀ P : OmegaPolymerType HF zK, 0 ≤ w P)
    (hr : r ∈ skeleton HF Q.val) :
    appendixFHoleHsharpWeightedTreeTerm HF zK w Q.val n ≤
      (((n + 1).factorial : ℝ))⁻¹ *
        ∑ X ∈ (Finset.univ :
            Finset (Fin (n + 1) → OmegaPolymerType HF zK)).filter
              (fun X => omegaClusterUnion HF zK X = Q.val),
          ∑ _T ∈ KP.spanningTrees
              (KP.incompGraph (omegaHolePolymerSystem HF zK) X),
            ∑ i : Fin (n + 1),
              if r ∈ skeleton HF (X i).val then
                ∏ j, w (X j)
              else
                0 := by
  classical
  have hfiber :
      (∑ X ∈ (Finset.univ :
          Finset (Fin (n + 1) → OmegaPolymerType HF zK)).filter
            (fun X => omegaClusterUnion HF zK X = Q.val),
        ∑ _T ∈ KP.spanningTrees
            (KP.incompGraph (omegaHolePolymerSystem HF zK) X),
          ∏ j, w (X j)) ≤
        ∑ X ∈ (Finset.univ :
            Finset (Fin (n + 1) → OmegaPolymerType HF zK)).filter
              (fun X => omegaClusterUnion HF zK X = Q.val),
          ∑ _T ∈ KP.spanningTrees
              (KP.incompGraph (omegaHolePolymerSystem HF zK) X),
            ∑ i : Fin (n + 1),
              if r ∈ skeleton HF (X i).val then
                ∏ j, w (X j)
              else
                0 := by
    refine Finset.sum_le_sum fun X hX => ?_
    have hXeq : omegaClusterUnion HF zK X = Q.val := (Finset.mem_filter.mp hX).2
    have hrUnion : r ∈ skeleton HF (omegaClusterUnion HF zK X) := by
      rw [hXeq]
      exact hr
    rw [omegaClusterUnion_skeleton HF zK X] at hrUnion
    rw [mem_biUnion] at hrUnion
    rcases hrUnion with ⟨i₀, _hi₀univ, hi₀⟩
    refine Finset.sum_le_sum fun _T _hT => ?_
    have hweight_nonneg : 0 ≤ ∏ j : Fin (n + 1), w (X j) :=
      Finset.prod_nonneg fun j _ => hw (X j)
    have hmarked_nonneg :
        ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))),
          0 ≤
            if r ∈ skeleton HF (X i).val then
              ∏ j, w (X j)
            else
              0 := by
      intro i _hi
      split_ifs
      · exact hweight_nonneg
      · exact le_rfl
    have hhit :
        (∏ j : Fin (n + 1), w (X j)) =
          if r ∈ skeleton HF (X i₀).val then
            ∏ j, w (X j)
          else
            0 := by
      rw [if_pos hi₀]
    refine (le_of_eq hhit).trans ?_
    exact Finset.single_le_sum
      (f := fun i : Fin (n + 1) =>
        if r ∈ skeleton HF (X i).val then
          ∏ j, w (X j)
        else
          0)
      hmarked_nonneg
      (Finset.mem_univ i₀)
  simpa [appendixFHoleHsharpWeightedTreeTerm] using
    mul_le_mul_of_nonneg_left hfiber (by positivity)

/-- Drop the fixed-union fiber after inserting the target-skeleton marker.
This is the finite bridge from a fixed target polymer `Q` to a sum over marked
coordinates.  The remaining task is to compare the coordinate-marked tree sums
with pinned KP/tree-walk estimates. -/
theorem appendixFHoleHsharpWeightedTreeTerm_le_markedIndexSum
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (Q : OmegaPolymerType HF zK)
    (r : Cube d L)
    (n : ℕ)
    (hw : ∀ P : OmegaPolymerType HF zK, 0 ≤ w P)
    (hr : r ∈ skeleton HF Q.val) :
    appendixFHoleHsharpWeightedTreeTerm HF zK w Q.val n ≤
      appendixFHoleHsharpWeightedTreeMarkedIndexSum HF zK w r n := by
  classical
  let all : Finset (Fin (n + 1) → OmegaPolymerType HF zK) := Finset.univ
  let fiber : Finset (Fin (n + 1) → OmegaPolymerType HF zK) :=
    all.filter (fun X => omegaClusterUnion HF zK X = Q.val)
  let trees (X : Fin (n + 1) → OmegaPolymerType HF zK) :=
    KP.spanningTrees (KP.incompGraph (omegaHolePolymerSystem HF zK) X)
  let W (X : Fin (n + 1) → OmegaPolymerType HF zK) : ℝ :=
    ∏ j, w (X j)
  let mark (X : Fin (n + 1) → OmegaPolymerType HF zK) (i : Fin (n + 1)) : Prop :=
    r ∈ skeleton HF (X i).val
  have hW_nonneg :
      ∀ X : Fin (n + 1) → OmegaPolymerType HF zK, 0 ≤ W X := by
    intro X
    exact Finset.prod_nonneg fun j _ => hw (X j)
  have htree_nonneg :
      ∀ X : Fin (n + 1) → OmegaPolymerType HF zK,
        0 ≤ ∑ _T ∈ trees X, W X := by
    intro X
    exact Finset.sum_nonneg fun _T _hT => hW_nonneg X
  have hcoord :
      ∀ i : Fin (n + 1),
        (∑ X ∈ fiber,
          ∑ _T ∈ trees X,
            if mark X i then W X else 0) ≤
          ∑ X ∈ all.filter (fun X => mark X i),
            ∑ _T ∈ trees X, W X := by
    intro i
    calc
      (∑ X ∈ fiber,
        ∑ _T ∈ trees X,
          if mark X i then W X else 0)
          = ∑ X ∈ fiber,
              if mark X i then
                ∑ _T ∈ trees X, W X
              else
                0 := by
            refine Finset.sum_congr rfl fun X _hX => ?_
            by_cases hmark : mark X i
            · simp [hmark]
            · simp [hmark]
      _ = ∑ X ∈ fiber.filter (fun X => mark X i),
              ∑ _T ∈ trees X, W X := by
            exact (Finset.sum_filter _ _).symm
      _ ≤ ∑ X ∈ all.filter (fun X => mark X i),
            ∑ _T ∈ trees X, W X := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
            · intro X hX
              have hx := (Finset.mem_filter.mp hX).2
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ X, hx⟩
            · intro X _hx_not_fiber _hx_marked
              exact htree_nonneg X
  have hmarked_inner :
      (∑ X ∈ fiber,
        ∑ _T ∈ trees X,
          ∑ i : Fin (n + 1),
            if mark X i then W X else 0) ≤
        ∑ i : Fin (n + 1),
          ∑ X ∈ all.filter (fun X => mark X i),
            ∑ _T ∈ trees X, W X := by
    calc
      (∑ X ∈ fiber,
        ∑ _T ∈ trees X,
          ∑ i : Fin (n + 1),
            if mark X i then W X else 0)
          = ∑ X ∈ fiber,
              ∑ i : Fin (n + 1),
                ∑ _T ∈ trees X,
                  if mark X i then W X else 0 := by
            refine Finset.sum_congr rfl fun X _hX => ?_
            exact Finset.sum_comm
      _ = ∑ i : Fin (n + 1),
            ∑ X ∈ fiber,
              ∑ _T ∈ trees X,
                if mark X i then W X else 0 := by
            exact Finset.sum_comm
      _ ≤ ∑ i : Fin (n + 1),
            ∑ X ∈ all.filter (fun X => mark X i),
              ∑ _T ∈ trees X, W X := by
            exact Finset.sum_le_sum fun i _hi => hcoord i
  have hmarked :=
    appendixFHoleHsharpWeightedTreeTerm_le_markedSkeletonSum
      HF zK w Q r n hw hr
  refine hmarked.trans ?_
  simpa [appendixFHoleHsharpWeightedTreeMarkedIndexSum, all, fiber, trees, W, mark] using
    mul_le_mul_of_nonneg_left hmarked_inner (by positivity)

end YangMills.RG
