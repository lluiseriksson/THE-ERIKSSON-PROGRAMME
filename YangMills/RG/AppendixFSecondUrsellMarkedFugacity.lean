/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFSecondUrsellWeightedTree
import YangMills.KP.RootedLeafSummation
import YangMills.KP.RootedCatalanExact

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

/-- Root-coordinate marked vertex-product sum, with the tree shape forgotten.
The aggregate rooted-child factorial estimate bounds the whole tree-shape
factor by `4^n`; this is the finite object left after that summation. -/
noncomputable def appendixFHoleHsharpWeightedTreeMarkedRootVertexSum
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (r : Cube d L)
    (n : ℕ) : ℝ :=
  ∑ X ∈ (Finset.univ :
      Finset (Fin (n + 1) → OmegaPolymerType HF zK)).filter
        (fun X => r ∈ skeleton HF (X 0).val),
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

/-- Root-coordinate marked tree sum with the child-order assignments made
explicit.  The sum over `KP.rootedChildOrderAssignments T` is only finite
bookkeeping; the next leaf-summation step can map its local choices into this
object before applying the factorial-price theorem. -/
noncomputable def appendixFHoleHsharpWeightedTreeMarkedRootChildOrderSum
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
        ∑ _π : KP.rootedChildOrderAssignments T,
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

/-- The explicit child-order assignment sum is exactly the child-factorial
marked root sum. -/
theorem appendixFHoleHsharpWeightedTreeMarkedRootChildOrderSum_eq_childFactorSum
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (r : Cube d L)
    (n : ℕ) :
    appendixFHoleHsharpWeightedTreeMarkedRootChildOrderSum HF zK w r n =
      appendixFHoleHsharpWeightedTreeMarkedRootChildFactorSum HF zK w r n := by
  classical
  unfold appendixFHoleHsharpWeightedTreeMarkedRootChildOrderSum
    appendixFHoleHsharpWeightedTreeMarkedRootChildFactorSum
  congr 1
  refine Finset.sum_congr rfl fun X _hX => ?_
  refine Finset.sum_congr rfl fun T _hT => ?_
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    KP.card_rootedChildOrderAssignments]
  push_cast
  rfl

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

/-- Child-order assignment form of the rooted child-factorial price.  This is
the version consumed by future leaf-summation maps whose choices are actual
orders of the rooted child fibers rather than an abstract factorial product. -/
theorem appendixFHoleHsharpWeightedTreeMarkedRootChildOrderSum_le_inv_succ_mul_rawSum
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (r : Cube d L)
    (n : ℕ)
    (hw : ∀ P : OmegaPolymerType HF zK, 0 ≤ w P) :
    appendixFHoleHsharpWeightedTreeMarkedRootChildOrderSum HF zK w r n ≤
      (((n : ℝ) + 1)⁻¹) *
        appendixFHoleHsharpWeightedTreeMarkedRootRawSum HF zK w r n := by
  rw [appendixFHoleHsharpWeightedTreeMarkedRootChildOrderSum_eq_childFactorSum]
  exact appendixFHoleHsharpWeightedTreeMarkedRootChildFactorSum_le_inv_succ_mul_rawSum
    HF zK w r n hw

/-- Aggregate rooted child-factorial consumer.  After forgetting the
fixed tuple's incompatibility graph into the complete graph, the total
child-factorial cost over all rooted tree shapes is bounded by `4^n` under the
second-Ursell normalization.  Thus the child-factor marked root sum is bounded
by the root-marked vertex-product sum with the explicit factor `4^n/(n+1)`.

This is purely finite overcounting: no leaf/source summability theorem or
Yang--Mills activity estimate is used here. -/
theorem appendixFHoleHsharpWeightedTreeMarkedRootChildFactorSum_le_four_pow_inv_succ_mul_vertexSum
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (r : Cube d L)
    (n : ℕ)
    (hw : ∀ P : OmegaPolymerType HF zK, 0 ≤ w P) :
    appendixFHoleHsharpWeightedTreeMarkedRootChildFactorSum HF zK w r n ≤
      ((((n : ℝ) + 1)⁻¹) * (4 : ℝ) ^ n) *
        appendixFHoleHsharpWeightedTreeMarkedRootVertexSum HF zK w r n := by
  classical
  let P := omegaHolePolymerSystem HF zK
  let all : Finset (Fin (n + 1) → OmegaPolymerType HF zK) := Finset.univ
  let marked : Finset (Fin (n + 1) → OmegaPolymerType HF zK) :=
    all.filter (fun X => r ∈ skeleton HF (X 0).val)
  let trees (X : Fin (n + 1) → OmegaPolymerType HF zK) :=
    KP.spanningTrees (KP.incompGraph P X)
  let topTrees : Finset (Finset (Sym2 (Fin (n + 1)))) :=
    KP.spanningTrees (⊤ : SimpleGraph (Fin (n + 1)))
  let W (X : Fin (n + 1) → OmegaPolymerType HF zK) : ℝ := ∏ j, w (X j)
  let C (T : Finset (Sym2 (Fin (n + 1)))) : ℝ :=
    ∏ v : Fin (n + 1), ((KP.rootedChildCount T v).factorial : ℝ)
  let invFact : ℝ := (((n + 1).factorial : ℝ))⁻¹
  let B : ℝ := (((n : ℝ) + 1)⁻¹) * (4 : ℝ) ^ n
  have hW : ∀ X, 0 ≤ W X := by
    intro X
    exact Finset.prod_nonneg fun j _ => hw (X j)
  have hC_nonneg : ∀ T, 0 ≤ C T := by
    intro T
    exact Finset.prod_nonneg fun v _ => Nat.cast_nonneg _
  have htrees_subset_top : ∀ X, trees X ⊆ topTrees := by
    intro X T hT
    have hT' : T ∈ KP.spanningTrees (KP.incompGraph P X) := by
      simpa [trees] using hT
    unfold KP.spanningTrees at hT'
    unfold topTrees KP.spanningTrees
    rw [Finset.mem_filter, Finset.mem_powerset] at hT' ⊢
    refine ⟨?_, hT'.2⟩
    intro e he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top,
      Set.mem_compl_iff, Sym2.mem_diagSet]
    have hmem : e ∈ (KP.incompGraph P X).edgeFinset := hT'.1 he
    rw [SimpleGraph.mem_edgeFinset] at hmem
    exact (KP.incompGraph P X).not_isDiag_of_mem_edgeSet hmem
  have htop :
      invFact * (∑ T ∈ topTrees, C T) ≤ B := by
    have hagg := KP.rootedChildCount_factorialTreeSum_normalized_le_four_pow n
    have hagg' :
        ((n : ℝ) + 1) * (invFact * (∑ T ∈ topTrees, C T)) ≤
          (4 : ℝ) ^ n := by
      simpa [topTrees, C, invFact, mul_assoc] using hagg
    have hpos : 0 < (n : ℝ) + 1 := by positivity
    calc
      invFact * (∑ T ∈ topTrees, C T)
          = (((n : ℝ) + 1)⁻¹) *
              (((n : ℝ) + 1) *
                (invFact * (∑ T ∈ topTrees, C T))) := by
            rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
      _ ≤ (((n : ℝ) + 1)⁻¹) * (4 : ℝ) ^ n := by
            exact mul_le_mul_of_nonneg_left hagg' (by positivity)
      _ = B := rfl
  have htreeFactor : ∀ X,
      invFact * (∑ T ∈ trees X, C T) ≤ B := by
    intro X
    have hsub :
        (∑ T ∈ trees X, C T) ≤ ∑ T ∈ topTrees, C T :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (htrees_subset_top X)
        (fun T _hT _hnot => hC_nonneg T)
    calc
      invFact * (∑ T ∈ trees X, C T)
          ≤ invFact * (∑ T ∈ topTrees, C T) := by
            exact mul_le_mul_of_nonneg_left hsub (by positivity)
      _ ≤ B := htop
  have hpoint : ∀ X ∈ marked,
      invFact * (∑ T ∈ trees X, C T * W X) ≤ B * W X := by
    intro X _hX
    have hsum :
        (∑ T ∈ trees X, C T * W X) =
          (∑ T ∈ trees X, C T) * W X := by
      rw [← Finset.sum_mul]
    calc
      invFact * (∑ T ∈ trees X, C T * W X)
          = (invFact * (∑ T ∈ trees X, C T)) * W X := by
            rw [hsum]
            ring
      _ ≤ B * W X := by
            exact mul_le_mul_of_nonneg_right (htreeFactor X) (hW X)
  calc
    appendixFHoleHsharpWeightedTreeMarkedRootChildFactorSum HF zK w r n
        = ∑ X ∈ marked, invFact * (∑ T ∈ trees X, C T * W X) := by
          simp [appendixFHoleHsharpWeightedTreeMarkedRootChildFactorSum,
            marked, all, trees, W, C, P, invFact, Finset.mul_sum]
    _ ≤ ∑ X ∈ marked, B * W X := by
          exact Finset.sum_le_sum fun X hX => hpoint X hX
    _ = B * ∑ X ∈ marked, W X := by
          rw [Finset.mul_sum]
    _ = B * appendixFHoleHsharpWeightedTreeMarkedRootVertexSum HF zK w r n := by
          simp [appendixFHoleHsharpWeightedTreeMarkedRootVertexSum,
            marked, all, W, B]

/-- Catalan-strengthened aggregate rooted child-factorial consumer.  This is
the same finite overcounting bridge as
`appendixFHoleHsharpWeightedTreeMarkedRootChildFactorSum_le_four_pow_inv_succ_mul_vertexSum`,
but it uses the exact rooted child-factorial Catalan identity in place of the
coarser `4^n` envelope. -/
theorem appendixFHoleHsharpWeightedTreeMarkedRootChildFactorSum_le_catalan_inv_succ_mul_vertexSum
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (r : Cube d L)
    (n : ℕ)
    (hw : ∀ P : OmegaPolymerType HF zK, 0 ≤ w P) :
    appendixFHoleHsharpWeightedTreeMarkedRootChildFactorSum HF zK w r n ≤
      ((((n : ℝ) + 1)⁻¹) * (catalan n : ℝ)) *
        appendixFHoleHsharpWeightedTreeMarkedRootVertexSum HF zK w r n := by
  classical
  let P := omegaHolePolymerSystem HF zK
  let all : Finset (Fin (n + 1) → OmegaPolymerType HF zK) := Finset.univ
  let marked : Finset (Fin (n + 1) → OmegaPolymerType HF zK) :=
    all.filter (fun X => r ∈ skeleton HF (X 0).val)
  let trees (X : Fin (n + 1) → OmegaPolymerType HF zK) :=
    KP.spanningTrees (KP.incompGraph P X)
  let topTrees : Finset (Finset (Sym2 (Fin (n + 1)))) :=
    KP.spanningTrees (⊤ : SimpleGraph (Fin (n + 1)))
  let W (X : Fin (n + 1) → OmegaPolymerType HF zK) : ℝ := ∏ j, w (X j)
  let C (T : Finset (Sym2 (Fin (n + 1)))) : ℝ :=
    ∏ v : Fin (n + 1), ((KP.rootedChildCount T v).factorial : ℝ)
  let invFact : ℝ := (((n + 1).factorial : ℝ))⁻¹
  let B : ℝ := (((n : ℝ) + 1)⁻¹) * (catalan n : ℝ)
  have hW : ∀ X, 0 ≤ W X := by
    intro X
    exact Finset.prod_nonneg fun j _ => hw (X j)
  have hC_nonneg : ∀ T, 0 ≤ C T := by
    intro T
    exact Finset.prod_nonneg fun v _ => Nat.cast_nonneg _
  have htrees_subset_top : ∀ X, trees X ⊆ topTrees := by
    intro X T hT
    have hT' : T ∈ KP.spanningTrees (KP.incompGraph P X) := by
      simpa [trees] using hT
    unfold KP.spanningTrees at hT'
    unfold topTrees KP.spanningTrees
    rw [Finset.mem_filter, Finset.mem_powerset] at hT' ⊢
    refine ⟨?_, hT'.2⟩
    intro e he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top,
      Set.mem_compl_iff, Sym2.mem_diagSet]
    have hmem : e ∈ (KP.incompGraph P X).edgeFinset := hT'.1 he
    rw [SimpleGraph.mem_edgeFinset] at hmem
    exact (KP.incompGraph P X).not_isDiag_of_mem_edgeSet hmem
  have htop :
      invFact * (∑ T ∈ topTrees, C T) ≤ B := by
    have hagg := KP.rootedChildCount_factorialTreeSum_normalized_le_catalan n
    have hagg' :
        ((n : ℝ) + 1) * (invFact * (∑ T ∈ topTrees, C T)) ≤
          (catalan n : ℝ) := by
      simpa [topTrees, C, invFact, mul_assoc] using hagg
    have hpos : 0 < (n : ℝ) + 1 := by positivity
    calc
      invFact * (∑ T ∈ topTrees, C T)
          = (((n : ℝ) + 1)⁻¹) *
              (((n : ℝ) + 1) *
                (invFact * (∑ T ∈ topTrees, C T))) := by
            rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
      _ ≤ (((n : ℝ) + 1)⁻¹) * (catalan n : ℝ) := by
            exact mul_le_mul_of_nonneg_left hagg' (by positivity)
      _ = B := rfl
  have htreeFactor : ∀ X,
      invFact * (∑ T ∈ trees X, C T) ≤ B := by
    intro X
    have hsub :
        (∑ T ∈ trees X, C T) ≤ ∑ T ∈ topTrees, C T :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (htrees_subset_top X)
        (fun T _hT _hnot => hC_nonneg T)
    calc
      invFact * (∑ T ∈ trees X, C T)
          ≤ invFact * (∑ T ∈ topTrees, C T) := by
            exact mul_le_mul_of_nonneg_left hsub (by positivity)
      _ ≤ B := htop
  have hpoint : ∀ X ∈ marked,
      invFact * (∑ T ∈ trees X, C T * W X) ≤ B * W X := by
    intro X _hX
    have hsum :
        (∑ T ∈ trees X, C T * W X) =
          (∑ T ∈ trees X, C T) * W X := by
      rw [← Finset.sum_mul]
    calc
      invFact * (∑ T ∈ trees X, C T * W X)
          = (invFact * (∑ T ∈ trees X, C T)) * W X := by
            rw [hsum]
            ring
      _ ≤ B * W X := by
            exact mul_le_mul_of_nonneg_right (htreeFactor X) (hW X)
  calc
    appendixFHoleHsharpWeightedTreeMarkedRootChildFactorSum HF zK w r n
        = ∑ X ∈ marked, invFact * (∑ T ∈ trees X, C T * W X) := by
          simp [appendixFHoleHsharpWeightedTreeMarkedRootChildFactorSum,
            marked, all, trees, W, C, P, invFact, Finset.mul_sum]
    _ ≤ ∑ X ∈ marked, B * W X := by
          exact Finset.sum_le_sum fun X hX => hpoint X hX
    _ = B * ∑ X ∈ marked, W X := by
          rw [Finset.mul_sum]
    _ = B * appendixFHoleHsharpWeightedTreeMarkedRootVertexSum HF zK w r n := by
          simp [appendixFHoleHsharpWeightedTreeMarkedRootVertexSum,
            marked, all, W, B]

/-- Child-order assignment form of the aggregate rooted child-factorial
consumer. -/
theorem appendixFHoleHsharpWeightedTreeMarkedRootChildOrderSum_le_four_pow_inv_succ_mul_vertexSum
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (r : Cube d L)
    (n : ℕ)
    (hw : ∀ P : OmegaPolymerType HF zK, 0 ≤ w P) :
    appendixFHoleHsharpWeightedTreeMarkedRootChildOrderSum HF zK w r n ≤
      ((((n : ℝ) + 1)⁻¹) * (4 : ℝ) ^ n) *
        appendixFHoleHsharpWeightedTreeMarkedRootVertexSum HF zK w r n := by
  rw [appendixFHoleHsharpWeightedTreeMarkedRootChildOrderSum_eq_childFactorSum]
  exact
    appendixFHoleHsharpWeightedTreeMarkedRootChildFactorSum_le_four_pow_inv_succ_mul_vertexSum
      HF zK w r n hw

/-- Child-order assignment form of the Catalan-strengthened aggregate rooted
child-factorial consumer. -/
theorem appendixFHoleHsharpWeightedTreeMarkedRootChildOrderSum_le_catalan_inv_succ_mul_vertexSum
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (r : Cube d L)
    (n : ℕ)
    (hw : ∀ P : OmegaPolymerType HF zK, 0 ≤ w P) :
    appendixFHoleHsharpWeightedTreeMarkedRootChildOrderSum HF zK w r n ≤
      ((((n : ℝ) + 1)⁻¹) * (catalan n : ℝ)) *
        appendixFHoleHsharpWeightedTreeMarkedRootVertexSum HF zK w r n := by
  rw [appendixFHoleHsharpWeightedTreeMarkedRootChildOrderSum_eq_childFactorSum]
  exact
    appendixFHoleHsharpWeightedTreeMarkedRootChildFactorSum_le_catalan_inv_succ_mul_vertexSum
      HF zK w r n hw

/-- The root-marked normalized tree sum is bounded by the child-factor version:
each rooted child factorial is at least `1`, so the inserted product of
factorials can only increase a nonnegative vertex weight. -/
theorem appendixFHoleHsharpWeightedTreeMarkedRootSum_le_childFactorSum
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (r : Cube d L)
    (n : ℕ)
    (hw : ∀ P : OmegaPolymerType HF zK, 0 ≤ w P) :
    appendixFHoleHsharpWeightedTreeMarkedRootSum HF zK w r n ≤
      appendixFHoleHsharpWeightedTreeMarkedRootChildFactorSum HF zK w r n := by
  classical
  let all : Finset (Fin (n + 1) → OmegaPolymerType HF zK) := Finset.univ
  let marked : Finset (Fin (n + 1) → OmegaPolymerType HF zK) :=
    all.filter (fun X => r ∈ skeleton HF (X 0).val)
  let trees (X : Fin (n + 1) → OmegaPolymerType HF zK) :=
    KP.spanningTrees (KP.incompGraph (omegaHolePolymerSystem HF zK) X)
  let W (X : Fin (n + 1) → OmegaPolymerType HF zK) : ℝ := ∏ j, w (X j)
  let C (T : Finset (Sym2 (Fin (n + 1)))) : ℝ :=
    ∏ v : Fin (n + 1), ((KP.rootedChildCount T v).factorial : ℝ)
  have hW : ∀ X, 0 ≤ W X := by
    intro X
    exact Finset.prod_nonneg fun j _ => hw (X j)
  have hC_one : ∀ T, 1 ≤ C T := by
    intro T
    dsimp [C]
    refine Finset.one_le_prod ?_
    intro v _hv
    exact_mod_cast
      (Nat.succ_le_of_lt
        (Nat.factorial_pos (KP.rootedChildCount T v)))
  have hsum :
      (∑ X ∈ marked, ∑ _T ∈ trees X, W X) ≤
        ∑ X ∈ marked, ∑ T ∈ trees X, C T * W X := by
    refine Finset.sum_le_sum ?_
    intro X _hX
    refine Finset.sum_le_sum ?_
    intro T _hT
    simpa [one_mul] using
      mul_le_mul_of_nonneg_right (hC_one T) (hW X)
  simpa [appendixFHoleHsharpWeightedTreeMarkedRootSum,
    appendixFHoleHsharpWeightedTreeMarkedRootChildFactorSum,
    marked, all, trees, W, C, Finset.mul_sum] using
    mul_le_mul_of_nonneg_left hsum (by positivity)

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

/-- Bare-target version of
`appendixFHoleHsharpWeightedTreeTerm_le_markedSkeletonSum`: if the marker
root belongs to the active skeleton of the fixed target `Y`, then the
fixed-union weighted tree term is bounded by the same fixed-union term with a
marked target-skeleton coordinate inserted.  No `OmegaPolymerType` witness for
`Y` is needed. -/
theorem appendixFHoleHsharpWeightedTreeTerm_le_markedSkeletonSum_of_mem_skeleton
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (Y : Finset (Cube d L))
    (r : Cube d L)
    (n : ℕ)
    (hw : ∀ P : OmegaPolymerType HF zK, 0 ≤ w P)
    (hr : r ∈ skeleton HF Y) :
    appendixFHoleHsharpWeightedTreeTerm HF zK w Y n ≤
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
                0 := by
  classical
  have hfiber :
      (∑ X ∈ (Finset.univ :
          Finset (Fin (n + 1) → OmegaPolymerType HF zK)).filter
            (fun X => omegaClusterUnion HF zK X = Y),
        ∑ _T ∈ KP.spanningTrees
            (KP.incompGraph (omegaHolePolymerSystem HF zK) X),
          ∏ j, w (X j)) ≤
        ∑ X ∈ (Finset.univ :
            Finset (Fin (n + 1) → OmegaPolymerType HF zK)).filter
              (fun X => omegaClusterUnion HF zK X = Y),
          ∑ _T ∈ KP.spanningTrees
              (KP.incompGraph (omegaHolePolymerSystem HF zK) X),
            ∑ i : Fin (n + 1),
              if r ∈ skeleton HF (X i).val then
                ∏ j, w (X j)
              else
                0 := by
    refine Finset.sum_le_sum fun X hX => ?_
    have hXeq : omegaClusterUnion HF zK X = Y := (Finset.mem_filter.mp hX).2
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

/-- Bare-target named form: marker insertion into the fixed-union
target-skeleton tree term without requiring a polymer witness for `Y`. -/
theorem appendixFHoleHsharpWeightedTreeTerm_le_markedSkeletonTreeTerm_of_mem_skeleton
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (Y : Finset (Cube d L))
    (r : Cube d L)
    (n : ℕ)
    (hw : ∀ P : OmegaPolymerType HF zK, 0 ≤ w P)
    (hr : r ∈ skeleton HF Y) :
    appendixFHoleHsharpWeightedTreeTerm HF zK w Y n ≤
      appendixFHoleHsharpMarkedSkeletonTreeTerm HF zK w r Y n := by
  simpa [appendixFHoleHsharpMarkedSkeletonTreeTerm] using
    appendixFHoleHsharpWeightedTreeTerm_le_markedSkeletonSum_of_mem_skeleton
      HF zK w Y r n hw hr

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

/-- Bare-target version of the marked-index reduction.  The fixed target `Y`
is still present during marker insertion and only the subsequent overcounting
forgets the fixed-union fiber. -/
theorem appendixFHoleHsharpWeightedTreeTerm_le_markedIndexSum_of_mem_skeleton
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (Y : Finset (Cube d L))
    (r : Cube d L)
    (n : ℕ)
    (hw : ∀ P : OmegaPolymerType HF zK, 0 ≤ w P)
    (hr : r ∈ skeleton HF Y) :
    appendixFHoleHsharpWeightedTreeTerm HF zK w Y n ≤
      appendixFHoleHsharpWeightedTreeMarkedIndexSum HF zK w r n := by
  exact
    (appendixFHoleHsharpWeightedTreeTerm_le_markedSkeletonTreeTerm_of_mem_skeleton
      HF zK w Y r n hw hr).trans
      (appendixFHoleHsharpMarkedSkeletonTreeTerm_le_markedIndexSum
        HF zK w Y r n hw)

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
  exact appendixFHoleHsharpWeightedTreeTerm_le_markedIndexSum_of_mem_skeleton
    HF zK w Q.val r n hw hr

/-- Bare-target weighted `H#` tree term reduced to the root-coordinate marked
tree sum.  This preserves the fixed target through marker insertion and only
then applies the finite coordinate symmetrization. -/
theorem appendixFHoleHsharpWeightedTreeTerm_le_card_mul_markedRootSum_of_mem_skeleton
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (Y : Finset (Cube d L))
    (r : Cube d L)
    (n : ℕ)
    (hw : ∀ P : OmegaPolymerType HF zK, 0 ≤ w P)
    (hr : r ∈ skeleton HF Y) :
    appendixFHoleHsharpWeightedTreeTerm HF zK w Y n ≤
      ((n : ℝ) + 1) *
        appendixFHoleHsharpWeightedTreeMarkedRootSum HF zK w r n := by
  exact
    (appendixFHoleHsharpWeightedTreeTerm_le_markedIndexSum_of_mem_skeleton
      HF zK w Y r n hw hr).trans_eq
      (appendixFHoleHsharpWeightedTreeMarkedIndexSum_eq_card_mul_root
        HF zK w r n)

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
    appendixFHoleHsharpWeightedTreeTerm_le_card_mul_markedRootSum_of_mem_skeleton
      HF zK w Q.val r n hw hr

/-- Fixed-target weighted tree term reduced all the way to the root-marked
vertex-product sum.  The factor `4^n` is exactly the aggregate rooted
child-factorial tree-shape cost; no analytic leaf summation is used here. -/
theorem appendixFHoleHsharpWeightedTreeTerm_le_four_pow_markedRootVertexSum
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (Q : OmegaPolymerType HF zK)
    (r : Cube d L)
    (n : ℕ)
    (hw : ∀ P : OmegaPolymerType HF zK, 0 ≤ w P)
    (hr : r ∈ skeleton HF Q.val) :
    appendixFHoleHsharpWeightedTreeTerm HF zK w Q.val n ≤
      (4 : ℝ) ^ n *
        appendixFHoleHsharpWeightedTreeMarkedRootVertexSum HF zK w r n := by
  have hmarked :
      appendixFHoleHsharpWeightedTreeTerm HF zK w Q.val n ≤
        ((n : ℝ) + 1) *
          appendixFHoleHsharpWeightedTreeMarkedRootSum HF zK w r n :=
    appendixFHoleHsharpWeightedTreeTerm_le_card_mul_markedRootSum
      HF zK w Q r n hw hr
  have hroot_child :
      appendixFHoleHsharpWeightedTreeMarkedRootSum HF zK w r n ≤
        appendixFHoleHsharpWeightedTreeMarkedRootChildFactorSum HF zK w r n :=
    appendixFHoleHsharpWeightedTreeMarkedRootSum_le_childFactorSum
      HF zK w r n hw
  have hchild_vertex :
      appendixFHoleHsharpWeightedTreeMarkedRootChildFactorSum HF zK w r n ≤
        ((((n : ℝ) + 1)⁻¹) * (4 : ℝ) ^ n) *
          appendixFHoleHsharpWeightedTreeMarkedRootVertexSum HF zK w r n :=
    appendixFHoleHsharpWeightedTreeMarkedRootChildFactorSum_le_four_pow_inv_succ_mul_vertexSum
      HF zK w r n hw
  have hpos : 0 < (n : ℝ) + 1 := by positivity
  calc
    appendixFHoleHsharpWeightedTreeTerm HF zK w Q.val n
        ≤ ((n : ℝ) + 1) *
          appendixFHoleHsharpWeightedTreeMarkedRootSum HF zK w r n := hmarked
    _ ≤ ((n : ℝ) + 1) *
          appendixFHoleHsharpWeightedTreeMarkedRootChildFactorSum HF zK w r n := by
          exact mul_le_mul_of_nonneg_left hroot_child hpos.le
    _ ≤ ((n : ℝ) + 1) *
          (((((n : ℝ) + 1)⁻¹) * (4 : ℝ) ^ n) *
            appendixFHoleHsharpWeightedTreeMarkedRootVertexSum HF zK w r n) := by
          exact mul_le_mul_of_nonneg_left hchild_vertex hpos.le
    _ = (4 : ℝ) ^ n *
          appendixFHoleHsharpWeightedTreeMarkedRootVertexSum HF zK w r n := by
          rw [mul_assoc, ← mul_assoc ((n : ℝ) + 1) (((n : ℝ) + 1)⁻¹)]
          rw [mul_inv_cancel₀ hpos.ne', one_mul]

/-- Catalan-strengthened fixed-target weighted tree term reduced to the
root-marked vertex-product sum.  This is the exact same finite reduction as
`appendixFHoleHsharpWeightedTreeTerm_le_four_pow_markedRootVertexSum`, with
the complete tree-shape entropy priced by `catalan n` instead of `4^n`. -/
theorem appendixFHoleHsharpWeightedTreeTerm_le_catalan_markedRootVertexSum
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (Q : OmegaPolymerType HF zK)
    (r : Cube d L)
    (n : ℕ)
    (hw : ∀ P : OmegaPolymerType HF zK, 0 ≤ w P)
    (hr : r ∈ skeleton HF Q.val) :
    appendixFHoleHsharpWeightedTreeTerm HF zK w Q.val n ≤
      (catalan n : ℝ) *
        appendixFHoleHsharpWeightedTreeMarkedRootVertexSum HF zK w r n := by
  have hmarked :
      appendixFHoleHsharpWeightedTreeTerm HF zK w Q.val n ≤
        ((n : ℝ) + 1) *
          appendixFHoleHsharpWeightedTreeMarkedRootSum HF zK w r n :=
    appendixFHoleHsharpWeightedTreeTerm_le_card_mul_markedRootSum
      HF zK w Q r n hw hr
  have hroot_child :
      appendixFHoleHsharpWeightedTreeMarkedRootSum HF zK w r n ≤
        appendixFHoleHsharpWeightedTreeMarkedRootChildFactorSum HF zK w r n :=
    appendixFHoleHsharpWeightedTreeMarkedRootSum_le_childFactorSum
      HF zK w r n hw
  have hchild_vertex :
      appendixFHoleHsharpWeightedTreeMarkedRootChildFactorSum HF zK w r n ≤
        ((((n : ℝ) + 1)⁻¹) * (catalan n : ℝ)) *
          appendixFHoleHsharpWeightedTreeMarkedRootVertexSum HF zK w r n :=
    appendixFHoleHsharpWeightedTreeMarkedRootChildFactorSum_le_catalan_inv_succ_mul_vertexSum
      HF zK w r n hw
  have hpos : 0 < (n : ℝ) + 1 := by positivity
  calc
    appendixFHoleHsharpWeightedTreeTerm HF zK w Q.val n
        ≤ ((n : ℝ) + 1) *
          appendixFHoleHsharpWeightedTreeMarkedRootSum HF zK w r n := hmarked
    _ ≤ ((n : ℝ) + 1) *
          appendixFHoleHsharpWeightedTreeMarkedRootChildFactorSum HF zK w r n := by
          exact mul_le_mul_of_nonneg_left hroot_child hpos.le
    _ ≤ ((n : ℝ) + 1) *
          (((((n : ℝ) + 1)⁻¹) * (catalan n : ℝ)) *
            appendixFHoleHsharpWeightedTreeMarkedRootVertexSum HF zK w r n) := by
          exact mul_le_mul_of_nonneg_left hchild_vertex hpos.le
    _ = (catalan n : ℝ) *
          appendixFHoleHsharpWeightedTreeMarkedRootVertexSum HF zK w r n := by
          rw [mul_assoc, ← mul_assoc ((n : ℝ) + 1) (((n : ℝ) + 1)⁻¹)]
          rw [mul_inv_cancel₀ hpos.ne', one_mul]

/-- Geometric wrapper for the vertex-product consumer.  A future source or
leaf-summation proof may bound the marked root vertex sum with ratio `Cleaf`;
the finite tree-shape aggregation turns this into the weighted tree estimate
with ratio `4 * Cleaf`.

This wrapper does not itself preserve target-polymer decay: the vertex sum
contains neither the fixed target nor the incompatibility tree.  A
target-dependent `decay` must therefore have been obtained before this
abstraction; the remaining global vertex sum is generally not volume-uniform. -/
theorem appendixFHoleHsharpWeightedTreeTerm_le_geometric_of_markedRootVertexSum
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (Q : OmegaPolymerType HF zK)
    (r : Cube d L)
    (n : ℕ)
    (Croot Cleaf decay : ℝ)
    (hw : ∀ P : OmegaPolymerType HF zK, 0 ≤ w P)
    (hr : r ∈ skeleton HF Q.val)
    (hvertex :
      appendixFHoleHsharpWeightedTreeMarkedRootVertexSum HF zK w r n ≤
        Croot * decay * Cleaf ^ n) :
    appendixFHoleHsharpWeightedTreeTerm HF zK w Q.val n ≤
      Croot * decay * ((4 : ℝ) * Cleaf) ^ n := by
  have hbase :=
    appendixFHoleHsharpWeightedTreeTerm_le_four_pow_markedRootVertexSum
      HF zK w Q r n hw hr
  have hscaled :
      (4 : ℝ) ^ n *
          appendixFHoleHsharpWeightedTreeMarkedRootVertexSum HF zK w r n ≤
        (4 : ℝ) ^ n * (Croot * decay * Cleaf ^ n) :=
    mul_le_mul_of_nonneg_left hvertex (pow_nonneg (by norm_num) n)
  exact hbase.trans (hscaled.trans_eq (by rw [mul_pow]; ring))

end YangMills.RG
