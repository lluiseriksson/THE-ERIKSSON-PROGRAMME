/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFSecondUrsellMarkedFugacity
import YangMills.RG.AppendixFSecondUrsellGeometry
import YangMills.KP.PenroseFiber

/-!
# Appendix F second-Ursell leaf-summation input

This module exposes the hard-core neighbor estimate from
`AppendixFSecondUrsellGeometry` as a nonnegative incompatibility kernel.  This
is the finite input needed by later rooted leaf-summation arguments: the local
choice at a child vertex can be read as a full-universe sum with an explicit
zero outside the incompatible fiber.

No source theorem, continuum statement, or infinite tree summation is added
here.  The only analytic content is the already-proved finite hard-core
metric-moment estimate, repackaged for downstream tree recursions.  The
moment-lift lemma records the elementary bookkeeping needed when a child
subtree leaves a power of the child metric to be summed at the parent edge.
The final two lemmas in this file are the target-decay composition layer:
extract the fixed-union exponential first, then consume any marked-root
leaf-summation estimate.
We also expose a parent-oriented complete-tree overcount that keeps the
hard-core incompatibility indicators on BFS parent edges instead of erasing
them into a vertex-product sum.

Oracle target: `[propext, Classical.choice, Quot.sound]`.
-/

attribute [local instance] Classical.propDecidable

open Finset
open scoped BigOperators
open SimpleGraph

namespace YangMills.RG

/-- Nonnegative child-choice kernel for a source-facing omega polymer `Q`.

It is the shifted metric moment times the spare exponential weight on `Q'`,
and is set to zero unless `Q'` is hard-core incompatible with `Q`. -/
noncomputable def appendixFHoleIncompMomentKernel
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ) (κ₀ : ℝ) (j : ℕ)
    (Q Q' : OmegaPolymerType HF zK) : ℝ :=
  if (omegaHolePolymerSystem HF zK).incomp Q Q' then
    (((discreteModifiedMetric HF Q'.val + 1 : ℕ) : ℝ) ^ j) *
      appendixFHoleExpWeight HF (2 * κ₀) Q'.val
  else
    0

/-- The child-choice kernel is pointwise nonnegative. -/
theorem appendixFHoleIncompMomentKernel_nonneg
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ) (κ₀ : ℝ) (j : ℕ)
    (Q Q' : OmegaPolymerType HF zK) :
    0 ≤ appendixFHoleIncompMomentKernel HF zK κ₀ j Q Q' := by
  classical
  by_cases hinc : (omegaHolePolymerSystem HF zK).incomp Q Q'
  · have hweight :
        0 ≤
          (((discreteModifiedMetric HF Q'.val + 1 : ℕ) : ℝ) ^ j) *
            appendixFHoleExpWeight HF (2 * κ₀) Q'.val := by
      exact mul_nonneg (pow_nonneg (by positivity) j)
        (appendixFHoleExpWeight_nonneg HF (2 * κ₀) Q'.val)
    simpa [appendixFHoleIncompMomentKernel, hinc] using hweight
  · simp [appendixFHoleIncompMomentKernel, hinc]

/-- Full-universe child-choice sum controlled by the finite hard-core
metric-moment estimate.  This is the form consumed by rooted leaf-summation:
the incompatibility condition has been moved into the kernel. -/
theorem appendixFHoleIncompMomentKernel_sum_le_factorial_mul
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (Q : OmegaPolymerType HF zK) (κ₀ : ℝ) (j : ℕ)
    (hκ₀ : 0 < κ₀)
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne : ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1) :
    (∑ Q' : OmegaPolymerType HF zK,
      appendixFHoleIncompMomentKernel HF zK κ₀ j Q Q')
      ≤
    (j.factorial : ℝ) *
      appendixFSecondUrsellMomentConstant d κ₀ ^ (j + 1) *
        (((discreteModifiedMetric HF Q.val + 1 : ℕ) : ℝ)) := by
  classical
  let p : OmegaPolymerType HF zK → Prop := fun Q' =>
    (omegaHolePolymerSystem HF zK).incomp Q Q'
  let w : OmegaPolymerType HF zK → ℝ := fun Q' =>
    (((discreteModifiedMetric HF Q'.val + 1 : ℕ) : ℝ) ^ j) *
      appendixFHoleExpWeight HF (2 * κ₀) Q'.val
  have hsum :
      (∑ Q' : OmegaPolymerType HF zK,
        appendixFHoleIncompMomentKernel HF zK κ₀ j Q Q')
        =
      (∑ Q' ∈ (Finset.univ : Finset (OmegaPolymerType HF zK)).filter p,
        w Q') := by
    calc
      (∑ Q' : OmegaPolymerType HF zK,
        appendixFHoleIncompMomentKernel HF zK κ₀ j Q Q')
          =
        ∑ Q' : OmegaPolymerType HF zK, if p Q' then w Q' else 0 := by
          simp [appendixFHoleIncompMomentKernel, p, w]
      _ =
        (∑ Q' ∈ (Finset.univ : Finset (OmegaPolymerType HF zK)).filter p,
          w Q') := by
          simpa using
            (Finset.sum_filter (s := (Finset.univ : Finset (OmegaPolymerType HF zK)))
              (p := p) (f := w)).symm
  rw [hsum]
  simpa [p, w] using
    appendixFHole_incomp_expWeight_metricMomentSum_le_factorial_mul
      HF zK Q κ₀ j hκ₀ hdisj hnoedges hholes_ne hCq

/-- Multiplying a child-choice kernel by an additional child metric moment is
the same as increasing its moment index.  This is the one-edge bookkeeping
identity used before applying the finite hard-core moment estimate. -/
theorem appendixFHoleIncompMomentKernel_childMoment_mul
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ) (κ₀ : ℝ) (j k : ℕ)
    (Q Q' : OmegaPolymerType HF zK) :
    (((discreteModifiedMetric HF Q'.val + 1 : ℕ) : ℝ) ^ k) *
      appendixFHoleIncompMomentKernel HF zK κ₀ j Q Q'
      =
    appendixFHoleIncompMomentKernel HF zK κ₀ (j + k) Q Q' := by
  classical
  by_cases hinc : (omegaHolePolymerSystem HF zK).incomp Q Q'
  · simp [appendixFHoleIncompMomentKernel, hinc, pow_add, mul_comm,
      mul_assoc]
  · simp [appendixFHoleIncompMomentKernel, hinc]

/-- Child-moment version of the hard-core kernel bound.  Any extra metric
moment produced by a child subtree can be absorbed into the factorial moment
index on the local parent-edge sum. -/
theorem appendixFHoleIncompMomentKernel_childMoment_sum_le_factorial_mul
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (Q : OmegaPolymerType HF zK) (κ₀ : ℝ) (j k : ℕ)
    (hκ₀ : 0 < κ₀)
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne : ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1) :
    (∑ Q' : OmegaPolymerType HF zK,
      (((discreteModifiedMetric HF Q'.val + 1 : ℕ) : ℝ) ^ k) *
        appendixFHoleIncompMomentKernel HF zK κ₀ j Q Q')
      ≤
    ((j + k).factorial : ℝ) *
      appendixFSecondUrsellMomentConstant d κ₀ ^ (j + k + 1) *
        (((discreteModifiedMetric HF Q.val + 1 : ℕ) : ℝ)) := by
  classical
  rw [Finset.sum_congr rfl (fun Q' _ =>
    appendixFHoleIncompMomentKernel_childMoment_mul HF zK κ₀ j k Q Q')]
  exact appendixFHoleIncompMomentKernel_sum_le_factorial_mul
    HF zK Q κ₀ (j + k) hκ₀ hdisj hnoedges hholes_ne hCq

/-- Complete-tree parent-oriented overcount for the marked root raw sum.

Compared with `appendixFHoleHsharpWeightedTreeMarkedRootRawSum`, this sum
forgets that the tree must be a spanning tree of the tuple's incompatibility
graph, but it keeps one explicit hard-core indicator on each BFS parent edge
of the complete-tree shape. -/
noncomputable def appendixFHoleHsharpWeightedTreeMarkedRootCompleteParentSum
    {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (r : Cube d L)
    (n : ℕ) : ℝ :=
  ∑ X ∈ (Finset.univ :
      Finset (Fin (n + 1) → OmegaPolymerType HF zK)).filter
        (fun X => r ∈ skeleton HF (X 0).val),
    ∑ T ∈ KP.spanningTrees (⊤ : SimpleGraph (Fin (n + 1))),
      (∏ v ∈ Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0),
        if (omegaHolePolymerSystem HF zK).incomp
            (X (KP.bfsParent T v)) (X v) then (1 : ℝ) else 0) *
        ∏ j, w (X j)

/-- The root-marked raw tree sum is bounded by the complete-tree parent
indicator sum.  This preserves the incompatibility data in a parent-indexed
form, preparing the fixed-tree leaf recursion without passing to the coarser
marked vertex-product sum. -/
theorem appendixFHoleHsharpWeightedTreeMarkedRootRawSum_le_completeTreeParentSum
    {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (r : Cube d L)
    (n : ℕ)
    (hw : ∀ Q : OmegaPolymerType HF zK, 0 ≤ w Q) :
    appendixFHoleHsharpWeightedTreeMarkedRootRawSum HF zK w r n ≤
      appendixFHoleHsharpWeightedTreeMarkedRootCompleteParentSum HF zK w r n := by
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
  let parentIndicator
      (X : Fin (n + 1) → OmegaPolymerType HF zK)
      (T : Finset (Sym2 (Fin (n + 1)))) : ℝ :=
    ∏ v ∈ Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0),
      if P.incomp (X (KP.bfsParent T v)) (X v) then (1 : ℝ) else 0
  have hW : ∀ X, 0 ≤ W X := by
    intro X
    exact Finset.prod_nonneg fun j _ => hw (X j)
  have hInd_nonneg : ∀ X T, 0 ≤ parentIndicator X T := by
    intro X T
    exact Finset.prod_nonneg fun v _ => by
      split_ifs <;> norm_num
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
  have hparent_eq_one :
      ∀ X T, T ∈ trees X → parentIndicator X T = 1 := by
    intro X T hT
    have hT' : T ∈ KP.spanningTrees (KP.incompGraph P X) := by
      simpa [trees] using hT
    let f : Sym2 (Fin (n + 1)) → ℝ := fun e =>
      if e ∈ (KP.incompGraph P X).edgeSet then (1 : ℝ) else 0
    have hedge_prod : (∏ e ∈ T, f e) = 1 := by
      refine Finset.prod_eq_one fun e he => ?_
      have hmem := KP.spanningTrees_subset (KP.incompGraph P X) hT' he
      rw [SimpleGraph.mem_edgeFinset] at hmem
      simp [f, hmem]
    have hparent_edges :
        (∏ v ∈ Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0),
          f (s(KP.bfsParent T v, v))) = parentIndicator X T := by
      have htree := KP.isTree_of_mem_spanningTrees (KP.incompGraph P X) hT'
      have hconn := htree.isConnected
      refine Finset.prod_congr rfl fun v hv => ?_
      rw [Finset.mem_filter] at hv
      have hne : KP.bfsParent T v ≠ v := by
        have hspec := (KP.bfsParent_spec hconn hv.2).2
        intro hEq
        rw [hEq] at hspec
        omega
      simp [f, P, SimpleGraph.mem_edgeSet,
        KP.incompGraph_adj, hne]
    calc
      parentIndicator X T
          = ∏ v ∈ Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0),
              f (s(KP.bfsParent T v, v)) := hparent_edges.symm
      _ = ∏ e ∈ T, f e := by
            exact (KP.prod_tree_eq_prod_parents hT' f).symm
      _ = 1 := hedge_prod
  have hpoint : ∀ X ∈ marked,
      (∑ T ∈ trees X, W X) ≤
        ∑ T ∈ topTrees, parentIndicator X T * W X := by
    intro X _hX
    calc
      (∑ T ∈ trees X, W X)
          = ∑ T ∈ trees X, parentIndicator X T * W X := by
              refine Finset.sum_congr rfl fun T hT => ?_
              rw [hparent_eq_one X T hT, one_mul]
      _ ≤ ∑ T ∈ topTrees, parentIndicator X T * W X :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (htrees_subset_top X)
            (fun T _hT _hnot =>
              mul_nonneg (hInd_nonneg X T) (hW X))
  calc
    appendixFHoleHsharpWeightedTreeMarkedRootRawSum HF zK w r n
        = ∑ X ∈ marked, ∑ T ∈ trees X, W X := by
          simp [appendixFHoleHsharpWeightedTreeMarkedRootRawSum,
            marked, all, trees, W, P]
    _ ≤ ∑ X ∈ marked, ∑ T ∈ topTrees, parentIndicator X T * W X := by
          exact Finset.sum_le_sum fun X hX => hpoint X hX
    _ = appendixFHoleHsharpWeightedTreeMarkedRootCompleteParentSum
          HF zK w r n := by
          simp [appendixFHoleHsharpWeightedTreeMarkedRootCompleteParentSum,
            marked, all, topTrees, parentIndicator, W, P]

/-- Kernelized complete-tree parent sum.  The root still carries the marked
root weight, while every nonroot child choice is charged through the
hard-core moment kernel with moment index `0`.

This is the finite object that the later fixed-tree leaf recursion should
consume with `appendixFHoleIncompMomentKernel_childMoment_sum_le_factorial_mul`.
-/
noncomputable def appendixFHoleHsharpWeightedTreeMarkedRootCompleteParentKernelSum
    {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (κ₀ : ℝ)
    (r : Cube d L)
    (n : ℕ) : ℝ :=
  ∑ X ∈ (Finset.univ :
      Finset (Fin (n + 1) → OmegaPolymerType HF zK)).filter
        (fun X => r ∈ skeleton HF (X 0).val),
    ∑ T ∈ KP.spanningTrees (⊤ : SimpleGraph (Fin (n + 1))),
      (∏ v ∈ Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0),
        appendixFHoleIncompMomentKernel HF zK κ₀ 0
          (X (KP.bfsParent T v)) (X v)) *
        w (X 0)

/-- If the vertex weight is bounded by the spare exponential weight used in
the hard-core moment kernel, the parent-oriented complete-tree overcount is
bounded by the kernelized complete-tree sum.  This is the bridge from the
finite tree overcount to the factorial-moment leaf estimates. -/
theorem appendixFHoleHsharpWeightedTreeMarkedRootCompleteParentSum_le_kernelSum
    {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (κ₀ : ℝ)
    (r : Cube d L)
    (n : ℕ)
    (hw : ∀ Q : OmegaPolymerType HF zK, 0 ≤ w Q)
    (hw_exp :
      ∀ Q : OmegaPolymerType HF zK,
        w Q ≤ appendixFHoleExpWeight HF (2 * κ₀) Q.val) :
    appendixFHoleHsharpWeightedTreeMarkedRootCompleteParentSum
        HF zK w r n ≤
      appendixFHoleHsharpWeightedTreeMarkedRootCompleteParentKernelSum
        HF zK w κ₀ r n := by
  classical
  let P := omegaHolePolymerSystem HF zK
  let all : Finset (Fin (n + 1) → OmegaPolymerType HF zK) := Finset.univ
  let marked : Finset (Fin (n + 1) → OmegaPolymerType HF zK) :=
    all.filter (fun X => r ∈ skeleton HF (X 0).val)
  let topTrees : Finset (Finset (Sym2 (Fin (n + 1)))) :=
    KP.spanningTrees (⊤ : SimpleGraph (Fin (n + 1)))
  let nonroot : Finset (Fin (n + 1)) :=
    Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0)
  let indicator
      (X : Fin (n + 1) → OmegaPolymerType HF zK)
      (T : Finset (Sym2 (Fin (n + 1)))) (v : Fin (n + 1)) : ℝ :=
    if P.incomp (X (KP.bfsParent T v)) (X v) then (1 : ℝ) else 0
  let kernel
      (X : Fin (n + 1) → OmegaPolymerType HF zK)
      (T : Finset (Sym2 (Fin (n + 1)))) (v : Fin (n + 1)) : ℝ :=
    appendixFHoleIncompMomentKernel HF zK κ₀ 0
      (X (KP.bfsParent T v)) (X v)
  have hfactor :
      ∀ X : Fin (n + 1) → OmegaPolymerType HF zK,
        ∏ j, w (X j) =
          (∏ v ∈ nonroot, w (X v)) * w (X 0) := by
    intro X
    dsimp [nonroot]
    rw [Finset.filter_ne',
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ 0)]
    ring
  have hleft_nonneg :
      ∀ X T v, 0 ≤ indicator X T v * w (X v) := by
    intro X T v
    exact mul_nonneg (by dsimp [indicator]; split_ifs <;> norm_num) (hw (X v))
  have hkernel_nonneg : ∀ X T v, 0 ≤ kernel X T v := by
    intro X T v
    exact appendixFHoleIncompMomentKernel_nonneg HF zK κ₀ 0
      (X (KP.bfsParent T v)) (X v)
  have hpoint_le :
      ∀ X T,
        (∏ v ∈ nonroot, indicator X T v) * ∏ j, w (X j) ≤
          (∏ v ∈ nonroot, kernel X T v) * w (X 0) := by
    intro X T
    have hprod_le :
        (∏ v ∈ nonroot, indicator X T v * w (X v)) ≤
          ∏ v ∈ nonroot, kernel X T v := by
      refine Finset.prod_le_prod ?_ ?_
      · intro v _hv
        exact hleft_nonneg X T v
      · intro v _hv
        by_cases hinc : P.incomp (X (KP.bfsParent T v)) (X v)
        · simpa [indicator, kernel, appendixFHoleIncompMomentKernel, P, hinc]
            using hw_exp (X v)
        · simp [indicator, kernel, appendixFHoleIncompMomentKernel, P, hinc]
    calc
      (∏ v ∈ nonroot, indicator X T v) * ∏ j, w (X j)
          = (∏ v ∈ nonroot, indicator X T v * w (X v)) * w (X 0) := by
            rw [hfactor X, ← mul_assoc, ← Finset.prod_mul_distrib]
      _ ≤ (∏ v ∈ nonroot, kernel X T v) * w (X 0) := by
            exact mul_le_mul_of_nonneg_right hprod_le (hw (X 0))
  calc
    appendixFHoleHsharpWeightedTreeMarkedRootCompleteParentSum HF zK w r n
        =
      ∑ X ∈ marked,
        ∑ T ∈ topTrees,
          (∏ v ∈ nonroot, indicator X T v) * ∏ j, w (X j) := by
          simp [appendixFHoleHsharpWeightedTreeMarkedRootCompleteParentSum,
            marked, all, topTrees, nonroot, indicator, P]
    _ ≤
      ∑ X ∈ marked,
        ∑ T ∈ topTrees,
          (∏ v ∈ nonroot, kernel X T v) * w (X 0) := by
          refine Finset.sum_le_sum fun X _hX => ?_
          refine Finset.sum_le_sum fun T _hT => ?_
          exact hpoint_le X T
    _ =
      appendixFHoleHsharpWeightedTreeMarkedRootCompleteParentKernelSum
        HF zK w κ₀ r n := by
          simp [appendixFHoleHsharpWeightedTreeMarkedRootCompleteParentKernelSum,
            marked, all, topTrees, nonroot, kernel]

/-- Target-decaying composition from a marked-root leaf-summation bound.

The order matters: first use the fixed-union metric stitching theorem to
extract the target exponential weight, and only then pass to the marked-root
overcount.  Thus the marked-root estimate may be proved later without needing
to remember the exact union fiber. -/
theorem appendixFHoleHsharpWeightedTreeTerm_le_geometric_of_markedRootLeafSummation
    {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w u : OmegaPolymerType HF zK → ℝ)
    (Y : Finset (Cube d L))
    (r : Cube d L)
    (n : ℕ)
    (rate Croot Cleaf : ℝ)
    (hrate : 0 ≤ rate)
    (hw : ∀ Q : OmegaPolymerType HF zK, 0 ≤ w Q)
    (hu : ∀ Q : OmegaPolymerType HF zK, 0 ≤ u Q)
    (hsplit :
      ∀ Q : OmegaPolymerType HF zK,
        w Q ≤ appendixFHoleExpWeight HF rate Q.val * u Q)
    (hr : r ∈ skeleton HF Y)
    (hleaf :
      ((n : ℝ) + 1) *
          appendixFHoleHsharpWeightedTreeMarkedRootSum
            HF zK u r n
        ≤ Croot * Cleaf ^ n) :
    appendixFHoleHsharpWeightedTreeTerm HF zK w Y n ≤
      Croot *
        appendixFHoleExpWeight HF rate Y *
        Cleaf ^ n := by
  calc
    appendixFHoleHsharpWeightedTreeTerm HF zK w Y n
        ≤ appendixFHoleExpWeight HF rate Y *
            appendixFHoleHsharpWeightedTreeTerm HF zK u Y n :=
      appendixFHoleHsharpWeightedTreeTerm_le_targetExpWeight_mul
        HF zK w u Y n rate hrate hw hu hsplit
    _ ≤ appendixFHoleExpWeight HF rate Y *
          (((n : ℝ) + 1) *
            appendixFHoleHsharpWeightedTreeMarkedRootSum
              HF zK u r n) := by
      exact mul_le_mul_of_nonneg_left
        (appendixFHoleHsharpWeightedTreeTerm_le_card_mul_markedRootSum_of_mem_skeleton
          HF zK u Y r n hu hr)
        (appendixFHoleExpWeight_nonneg HF rate Y)
    _ ≤ appendixFHoleExpWeight HF rate Y *
          (Croot * Cleaf ^ n) := by
      exact mul_le_mul_of_nonneg_left hleaf
        (appendixFHoleExpWeight_nonneg HF rate Y)
    _ = Croot *
          appendixFHoleExpWeight HF rate Y *
          Cleaf ^ n := by
      ring

/-- Nonempty-target version of
`appendixFHoleHsharpWeightedTreeTerm_le_geometric_of_markedRootLeafSummation`.
It chooses a skeleton root after the target exponential has been made
available, while requiring the marked-root bound uniformly over skeleton
roots. -/
theorem appendixFHoleHsharpWeightedTreeTerm_le_geometric_of_markedRootLeafSummation_of_skeleton_nonempty
    {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w u : OmegaPolymerType HF zK → ℝ)
    (Y : Finset (Cube d L))
    (n : ℕ)
    (rate Croot Cleaf : ℝ)
    (hrate : 0 ≤ rate)
    (hw : ∀ Q : OmegaPolymerType HF zK, 0 ≤ w Q)
    (hu : ∀ Q : OmegaPolymerType HF zK, 0 ≤ u Q)
    (hsplit :
      ∀ Q : OmegaPolymerType HF zK,
        w Q ≤ appendixFHoleExpWeight HF rate Q.val * u Q)
    (hY : (skeleton HF Y).Nonempty)
    (hleaf :
      ∀ r : Cube d L, r ∈ skeleton HF Y →
        ((n : ℝ) + 1) *
            appendixFHoleHsharpWeightedTreeMarkedRootSum
              HF zK u r n
          ≤ Croot * Cleaf ^ n) :
    appendixFHoleHsharpWeightedTreeTerm HF zK w Y n ≤
      Croot *
        appendixFHoleExpWeight HF rate Y *
        Cleaf ^ n := by
  classical
  rcases hY with ⟨r, hr⟩
  exact
    appendixFHoleHsharpWeightedTreeTerm_le_geometric_of_markedRootLeafSummation
      HF zK w u Y r n rate Croot Cleaf hrate hw hu hsplit hr
      (hleaf r hr)

end YangMills.RG
