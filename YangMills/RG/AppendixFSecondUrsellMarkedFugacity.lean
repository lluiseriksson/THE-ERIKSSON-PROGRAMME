/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFSecondUrsellWeightedTree
import YangMills.KP.RootedChildCount

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
open SimpleGraph
open scoped BigOperators

namespace YangMills.RG

variable {d L : ℕ} [NeZero L]

private lemma spanningTrees_image_perm_incomp
    (P : KP.PolymerSystem) {n : ℕ}
    (X : Fin n → P.Polymer) (σ : Equiv.Perm (Fin n))
    (E : Finset (Sym2 (Fin n))) :
    E.image (Sym2.map σ) ∈ KP.spanningTrees (KP.incompGraph P X) ↔
      E ∈ KP.spanningTrees (KP.incompGraph P (X ∘ σ)) := by
  classical
  have hmapinj : Function.Injective (Sym2.map σ) :=
    Sym2.map.injective σ.injective
  have hedge : ∀ i j : Fin n,
      (KP.incompGraph P (X ∘ σ)).Adj i j
        ↔ (KP.incompGraph P X).Adj (σ i) (σ j) := by
    intro i j
    rw [KP.incompGraph_adj, KP.incompGraph_adj]
    constructor
    · rintro ⟨hne, hinc⟩
      exact ⟨fun h => hne (σ.injective h), hinc⟩
    · rintro ⟨hne, hinc⟩
      exact ⟨fun h => hne (by rw [h]), hinc⟩
  have hadj : ∀ (F : Finset (Sym2 (Fin n))) (i j : Fin n),
      (SimpleGraph.fromEdgeSet
        (↑(F.image (Sym2.map σ)) : Set (Sym2 (Fin n)))).Adj (σ i) (σ j)
      ↔ (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 (Fin n)))).Adj i j := by
    intro F i j
    rw [SimpleGraph.fromEdgeSet_adj, SimpleGraph.fromEdgeSet_adj]
    constructor
    · rintro ⟨hmem, hne⟩
      refine ⟨?_, fun h => hne (by rw [h])⟩
      rw [Finset.mem_coe, Finset.mem_image] at hmem
      obtain ⟨e', he', heq⟩ := hmem
      have he : e' = s(i, j) := hmapinj (by rw [heq, Sym2.map_mk])
      rwa [he] at he'
    · rintro ⟨hmem, hne⟩
      refine ⟨?_, fun h => hne (σ.injective h)⟩
      rw [Finset.mem_coe, Finset.mem_image]
      exact ⟨s(i, j), hmem, rfl⟩
  have htree : ∀ F : Finset (Sym2 (Fin n)),
      (SimpleGraph.fromEdgeSet
        (↑(F.image (Sym2.map σ)) : Set (Sym2 (Fin n)))).IsTree
      ↔ (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 (Fin n)))).IsTree := by
    intro F
    have iso : SimpleGraph.fromEdgeSet (↑F : Set (Sym2 (Fin n)))
        ≃g SimpleGraph.fromEdgeSet
          (↑(F.image (Sym2.map σ)) : Set (Sym2 (Fin n))) :=
      { toEquiv := σ
        map_rel_iff' := by intro i j; exact hadj F i j }
    exact iso.isTree_iff.symm
  unfold KP.spanningTrees
  constructor
  · intro hE
    rw [Finset.mem_filter, Finset.mem_powerset] at hE ⊢
    refine ⟨?_, (htree E).mp hE.2⟩
    intro e he
    revert he
    refine Sym2.ind (fun i j he => ?_) e
    have hmem_image : Sym2.map σ s(i, j) ∈ (KP.incompGraph P X).edgeFinset := by
      exact hE.1 (Finset.mem_image.mpr ⟨s(i, j), he, rfl⟩)
    rw [Sym2.map_mk, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hmem_image
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact (hedge i j).mpr hmem_image
  · intro hE
    rw [Finset.mem_filter, Finset.mem_powerset] at hE ⊢
    refine ⟨?_, (htree E).mpr hE.2⟩
    intro e he
    rw [Finset.mem_image] at he
    obtain ⟨e', he', rfl⟩ := he
    revert he'
    refine Sym2.ind (fun i j he' => ?_) e'
    have hmem := hE.1 he'
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hmem
    rw [Sym2.map_mk, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact (hedge i j).mp hmem

private lemma weightedTreeSum_comp_perm
    (P : KP.PolymerSystem) {n : ℕ}
    (X : Fin n → P.Polymer) (σ : Equiv.Perm (Fin n))
    (w : P.Polymer → ℝ) :
    (∑ _T ∈ KP.spanningTrees (KP.incompGraph P (X ∘ σ)),
        ∏ j, w ((X ∘ σ) j)) =
      ∑ _T ∈ KP.spanningTrees (KP.incompGraph P X),
        ∏ j, w (X j) := by
  classical
  have hprod : (∏ j, w ((X ∘ σ) j)) = ∏ j, w (X j) :=
    Equiv.prod_comp σ (fun j => w (X j))
  refine Finset.sum_nbij'
    (i := fun T => T.image (Sym2.map σ))
    (j := fun T => T.image (Sym2.map σ.symm)) ?_ ?_ ?_ ?_ ?_
  · intro T hT
    exact (spanningTrees_image_perm_incomp P X σ T).mpr hT
  · intro T hT
    have hEimg : (T.image (Sym2.map σ.symm)).image (Sym2.map σ) = T := by
      rw [Finset.image_image, ← Sym2.map_comp, Equiv.self_comp_symm,
        Sym2.map_id, Finset.image_id]
    exact (spanningTrees_image_perm_incomp P X σ
      (T.image (Sym2.map σ.symm))).mp (by simpa [hEimg] using hT)
  · intro T _hT
    dsimp only
    rw [Finset.image_image, ← Sym2.map_comp, Equiv.symm_comp_self,
      Sym2.map_id, Finset.image_id]
  · intro T _hT
    dsimp only
    rw [Finset.image_image, ← Sym2.map_comp, Equiv.self_comp_symm,
      Sym2.map_id, Finset.image_id]
  · intro T _hT
    exact hprod

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

/-- Root-coordinate version of the target-skeleton marked weighted tree sum.
This is the form that the pinned KP/tree-walk machinery should consume next. -/
noncomputable def appendixFHoleHsharpWeightedTreeMarkedRootSum
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (r : Cube d L)
    (n : ℕ) : ℝ :=
  (((n + 1).factorial : ℝ))⁻¹ *
    ∑ X ∈ (Finset.univ :
        Finset (Fin (n + 1) → OmegaPolymerType HF zK)).filter
          (fun X => r ∈ skeleton HF (X 0).val),
      ∑ _T ∈ KP.spanningTrees
          (KP.incompGraph (omegaHolePolymerSystem HF zK) X),
        ∏ j, w (X j)

/-- Unnormalized root-coordinate marked weighted tree sum.  This is the raw
finite tree sum underlying `appendixFHoleHsharpWeightedTreeMarkedRootSum`,
before the second-Ursell `(n+1)!` normalization is applied. -/
noncomputable def appendixFHoleHsharpWeightedTreeMarkedRootRawSum
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (r : Cube d L)
    (n : ℕ) : ℝ :=
  ∑ X ∈ (Finset.univ :
      Finset (Fin (n + 1) → OmegaPolymerType HF zK)).filter
        (fun X => r ∈ skeleton HF (X 0).val),
    ∑ _T ∈ KP.spanningTrees
        (KP.incompGraph (omegaHolePolymerSystem HF zK) X),
      ∏ j, w (X j)

/-- Root-coordinate marked tree sum with the independent child-order
factorials inserted for each rooted BFS/Penrose tree.  The next leaf-summation
step can overcount by this term, while the theorem below prices the factorial
loss against the standard second-Ursell normalization. -/
noncomputable def appendixFHoleHsharpWeightedTreeMarkedRootChildFactorSum
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (r : Cube d L)
    (n : ℕ) : ℝ :=
  (((n + 1).factorial : ℝ))⁻¹ *
    ∑ X ∈ (Finset.univ :
        Finset (Fin (n + 1) → OmegaPolymerType HF zK)).filter
          (fun X => r ∈ skeleton HF (X 0).val),
      ∑ T ∈ KP.spanningTrees
          (KP.incompGraph (omegaHolePolymerSystem HF zK) X),
        (∏ v : Fin (n + 1), ((KP.rootedChildCount T v).factorial : ℝ)) *
          ∏ j, w (X j)

/-- The named raw-sum form of the root-marked tree term. -/
theorem appendixFHoleHsharpWeightedTreeMarkedRootSum_eq_inv_factorial_mul_rawSum
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (r : Cube d L)
    (n : ℕ) :
    appendixFHoleHsharpWeightedTreeMarkedRootSum HF zK w r n =
      (((n + 1).factorial : ℝ))⁻¹ *
        appendixFHoleHsharpWeightedTreeMarkedRootRawSum HF zK w r n := by
  simp [appendixFHoleHsharpWeightedTreeMarkedRootSum,
    appendixFHoleHsharpWeightedTreeMarkedRootRawSum]

/-- First consumer of the rooted child-factorial price.  If the vertex
weights are nonnegative, then inserting the independent child-order factorials
inside each rooted tree and applying the `(n+1)!` second-Ursell normalization
costs at most the single marked-root factor `(n+1)⁻¹` times the unnormalized
root-marked tree sum. -/
theorem appendixFHoleHsharpWeightedTreeMarkedRootChildFactorSum_le_inv_succ_mul_rawSum
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (r : Cube d L)
    (n : ℕ)
    (hw : ∀ P : OmegaPolymerType HF zK, 0 ≤ w P) :
    appendixFHoleHsharpWeightedTreeMarkedRootChildFactorSum HF zK w r n ≤
      (((n : ℝ) + 1)⁻¹) *
        appendixFHoleHsharpWeightedTreeMarkedRootRawSum HF zK w r n := by
  classical
  let all : Finset (Fin (n + 1) → OmegaPolymerType HF zK) := Finset.univ
  let marked : Finset (Fin (n + 1) → OmegaPolymerType HF zK) :=
    all.filter (fun X => r ∈ skeleton HF (X 0).val)
  let trees (X : Fin (n + 1) → OmegaPolymerType HF zK) :=
    KP.spanningTrees (KP.incompGraph (omegaHolePolymerSystem HF zK) X)
  let W (X : Fin (n + 1) → OmegaPolymerType HF zK) : ℝ := ∏ j, w (X j)
  let C (T : Finset (Sym2 (Fin (n + 1)))) : ℝ :=
    ∏ v : Fin (n + 1), ((KP.rootedChildCount T v).factorial : ℝ)
  let c : ℝ := (((n : ℝ) + 1)⁻¹)
  have hW : ∀ X, 0 ≤ W X := by
    intro X
    exact Finset.prod_nonneg fun j _ => hw (X j)
  have hpoint : ∀ X ∈ marked, ∀ T ∈ trees X,
      (((n + 1).factorial : ℝ))⁻¹ * (C T * W X) ≤ c * W X := by
    intro X _hX T _hT
    calc
      (((n + 1).factorial : ℝ))⁻¹ * (C T * W X)
          = ((((n + 1).factorial : ℝ))⁻¹ * C T) * W X := by ring
      _ ≤ c * W X := by
          exact mul_le_mul_of_nonneg_right
            (KP.rootedChildCount_factorialProduct_inv_succ_factorial_le_inv_succ T)
            (hW X)
  calc
    appendixFHoleHsharpWeightedTreeMarkedRootChildFactorSum HF zK w r n
        = ∑ X ∈ marked, ∑ T ∈ trees X,
            (((n + 1).factorial : ℝ))⁻¹ * (C T * W X) := by
          simp [appendixFHoleHsharpWeightedTreeMarkedRootChildFactorSum,
            marked, all, trees, W, C, Finset.mul_sum]
    _ ≤ ∑ X ∈ marked, ∑ T ∈ trees X, c * W X := by
          refine Finset.sum_le_sum fun X hX => ?_
          refine Finset.sum_le_sum fun T hT => ?_
          exact hpoint X hX T hT
    _ = ∑ X ∈ marked, c * ∑ T ∈ trees X, W X := by
          refine Finset.sum_congr rfl fun X _hX => ?_
          rw [Finset.mul_sum]
    _ = c * ∑ X ∈ marked, ∑ T ∈ trees X, W X := by
          rw [Finset.mul_sum]
    _ = c * appendixFHoleHsharpWeightedTreeMarkedRootRawSum HF zK w r n := by
          simp [appendixFHoleHsharpWeightedTreeMarkedRootRawSum,
            marked, all, trees, W]

/-- Fixed-union weighted tree term with an inserted target-skeleton marker.
This names the finite object produced by the marker-insertion step before the
fixed target-union fiber is forgotten. -/
noncomputable def appendixFHoleHsharpMarkedSkeletonTreeTerm
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (r : Cube d L)
    (Y : Finset (Cube d L))
    (n : ℕ) : ℝ :=
  (((n + 1).factorial : ℝ))⁻¹ *
    ∑ X ∈ (Finset.univ :
        Finset (Fin (n + 1) → OmegaPolymerType HF zK)).filter
          (fun X => omegaClusterUnion HF zK X = Y),
      ∑ _T ∈ KP.spanningTrees
          (KP.incompGraph (omegaHolePolymerSystem HF zK) X),
        ∑ i : Fin (n + 1),
          if r ∈ skeleton HF (X i).val then
            ∏ j, w (X j)
          else
            0

/-- Coordinate symmetry of the marked weighted tree sum.  A coordinate marked
at `i` is transported to the root coordinate by precomposing the tuple with
`Equiv.swap 0 i`; the private relabeling lemma transports the corresponding
spanning-tree sum. -/
theorem appendixFHoleHsharpWeightedTreeMarkedIndexSum_eq_card_mul_root
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (r : Cube d L)
    (n : ℕ) :
    appendixFHoleHsharpWeightedTreeMarkedIndexSum HF zK w r n =
      ((n : ℝ) + 1) *
        appendixFHoleHsharpWeightedTreeMarkedRootSum HF zK w r n := by
  classical
  let P := omegaHolePolymerSystem HF zK
  let slice (i : Fin (n + 1)) : ℝ :=
    ∑ X ∈ (Finset.univ :
        Finset (Fin (n + 1) → OmegaPolymerType HF zK)).filter
          (fun X => r ∈ skeleton HF (X i).val),
      ∑ _T ∈ KP.spanningTrees (KP.incompGraph P X),
        ∏ j, w (X j)
  have hidx : ∀ i : Fin (n + 1), slice i = slice 0 := by
    intro i
    let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 i
    refine Finset.sum_nbij' (i := fun X => X ∘ σ) (j := fun X => X ∘ σ)
      ?_ ?_ ?_ ?_ ?_
    · intro X hX
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have hi : r ∈ skeleton HF (X i).val := (Finset.mem_filter.mp hX).2
      have h0 : (X ∘ σ) 0 = X i := by
        simp [σ, Function.comp, Equiv.swap_apply_left]
      change r ∈ skeleton HF ((X ∘ σ) 0).val
      rwa [h0]
    · intro X hX
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have h0 : r ∈ skeleton HF (X 0).val := (Finset.mem_filter.mp hX).2
      have hi : (X ∘ σ) i = X 0 := by
        simp [σ, Function.comp, Equiv.swap_apply_right]
      change r ∈ skeleton HF ((X ∘ σ) i).val
      rwa [hi]
    · intro X _hX
      funext k
      simp [σ, Function.comp, Equiv.swap_apply_self]
    · intro X _hX
      funext k
      simp [σ, Function.comp, Equiv.swap_apply_self]
    · intro X _hX
      exact (weightedTreeSum_comp_perm P X σ w).symm
  have hsum :
      (∑ i : Fin (n + 1), slice i) =
        ∑ _i : Fin (n + 1), slice 0 := by
    exact Finset.sum_congr rfl fun i _hi => hidx i
  calc
    appendixFHoleHsharpWeightedTreeMarkedIndexSum HF zK w r n
        = (((n + 1).factorial : ℝ))⁻¹ * ∑ i : Fin (n + 1), slice i := by
          simp [appendixFHoleHsharpWeightedTreeMarkedIndexSum, slice, P]
    _ = (((n + 1).factorial : ℝ))⁻¹ * ∑ _i : Fin (n + 1), slice 0 := by
          rw [hsum]
    _ = ((n : ℝ) + 1) *
          appendixFHoleHsharpWeightedTreeMarkedRootSum HF zK w r n := by
          simp [appendixFHoleHsharpWeightedTreeMarkedRootSum, slice, P,
            Finset.sum_const, nsmul_eq_mul]
          ring

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

/-- Named form of `appendixFHoleHsharpWeightedTreeTerm_le_markedSkeletonSum`:
the fixed-target weighted tree term is bounded by the fixed-union marked
target-skeleton tree term. -/
theorem appendixFHoleHsharpWeightedTreeTerm_le_markedSkeletonTreeTerm
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (Q : OmegaPolymerType HF zK)
    (r : Cube d L)
    (n : ℕ)
    (hw : ∀ P : OmegaPolymerType HF zK, 0 ≤ w P)
    (hr : r ∈ skeleton HF Q.val) :
    appendixFHoleHsharpWeightedTreeTerm HF zK w Q.val n ≤
      appendixFHoleHsharpMarkedSkeletonTreeTerm HF zK w r Q.val n := by
  simpa [appendixFHoleHsharpMarkedSkeletonTreeTerm] using
    appendixFHoleHsharpWeightedTreeTerm_le_markedSkeletonSum
      HF zK w Q r n hw hr

/-- Forget the fixed target-union fiber after the target-skeleton marker has
been inserted.  This isolates the finite overcounting step from the marker
insertion itself. -/
theorem appendixFHoleHsharpMarkedSkeletonTreeTerm_le_markedIndexSum
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (Y : Finset (Cube d L))
    (r : Cube d L)
    (n : ℕ)
    (hw : ∀ P : OmegaPolymerType HF zK, 0 ≤ w P) :
    appendixFHoleHsharpMarkedSkeletonTreeTerm HF zK w r Y n ≤
      appendixFHoleHsharpWeightedTreeMarkedIndexSum HF zK w r n := by
  classical
  let all : Finset (Fin (n + 1) → OmegaPolymerType HF zK) := Finset.univ
  let fiber : Finset (Fin (n + 1) → OmegaPolymerType HF zK) :=
    all.filter (fun X => omegaClusterUnion HF zK X = Y)
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
  simpa [appendixFHoleHsharpMarkedSkeletonTreeTerm,
    appendixFHoleHsharpWeightedTreeMarkedIndexSum, all, fiber, trees, W, mark] using
    mul_le_mul_of_nonneg_left hmarked_inner (by positivity)

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
  exact
    (appendixFHoleHsharpWeightedTreeTerm_le_markedSkeletonTreeTerm
      HF zK w Q r n hw hr).trans
      (appendixFHoleHsharpMarkedSkeletonTreeTerm_le_markedIndexSum
        HF zK w Q.val r n hw)

/-- Fixed-target weighted `H#` tree term reduced to the root-coordinate marked
tree sum.  This is the finite pinned-coordinate consumer; the remaining
analytic task is to bound the root-marked tree sum by a KP/tree-walk or
fugacity estimate. -/
theorem appendixFHoleHsharpWeightedTreeTerm_le_card_mul_markedRootSum
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (Q : OmegaPolymerType HF zK)
    (r : Cube d L)
    (n : ℕ)
    (hw : ∀ P : OmegaPolymerType HF zK, 0 ≤ w P)
    (hr : r ∈ skeleton HF Q.val) :
    appendixFHoleHsharpWeightedTreeTerm HF zK w Q.val n ≤
      ((n : ℝ) + 1) *
        appendixFHoleHsharpWeightedTreeMarkedRootSum HF zK w r n := by
  exact
    (appendixFHoleHsharpWeightedTreeTerm_le_markedIndexSum
      HF zK w Q r n hw hr).trans_eq
      (appendixFHoleHsharpWeightedTreeMarkedIndexSum_eq_card_mul_root
        HF zK w r n)

end YangMills.RG
