/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFSecondUrsellMarkedFugacity
import YangMills.RG.AppendixFSecondUrsellGeometry
import YangMills.KP.PenroseFiber
import YangMills.KP.WalkBound
import YangMills.KP.RootedChildCount

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

/-- Normalized child-moment version of the hard-core kernel bound.

The parent metric denominator is the exact local factor used by the
fixed-tree parent recursion.  Dividing the child-moment estimate by this
positive metric removes the parent-size factor from the local budget. -/
theorem appendixFHoleIncompMomentKernel_normalizedChildMoment_sum_le_factorial_mul
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (Q : OmegaPolymerType HF zK)
    (κ₀ : ℝ)
    (j : ℕ)
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
      ((((discreteModifiedMetric HF Q'.val + 1 : ℕ) : ℝ) ^ j) *
          appendixFHoleIncompMomentKernel HF zK κ₀ 0 Q Q') /
        (((discreteModifiedMetric HF Q.val + 1 : ℕ) : ℝ)))
      ≤
    (j.factorial : ℝ) *
      appendixFSecondUrsellMomentConstant d κ₀ ^ (j + 1) := by
  classical
  let β := OmegaPolymerType HF zK
  let metric : β → ℝ := fun Q =>
    (((discreteModifiedMetric HF Q.val + 1 : ℕ) : ℝ))
  let A : ℝ :=
    (j.factorial : ℝ) *
      appendixFSecondUrsellMomentConstant d κ₀ ^ (j + 1)
  have hmetric_pos : 0 < metric Q := by
    positivity
  have hmoment :=
    appendixFHoleIncompMomentKernel_childMoment_sum_le_factorial_mul
      HF zK Q κ₀ 0 j hκ₀ hdisj hnoedges hholes_ne hCq
  have hdiv :
      (∑ Q' : β,
        metric Q' ^ j *
          appendixFHoleIncompMomentKernel HF zK κ₀ 0 Q Q') /
          metric Q ≤ A := by
    calc
      (∑ Q' : β,
        metric Q' ^ j *
          appendixFHoleIncompMomentKernel HF zK κ₀ 0 Q Q') /
          metric Q
          ≤ (A * metric Q) / metric Q := by
            exact div_le_div_of_nonneg_right
              (by simpa [A, metric, Nat.zero_add] using hmoment)
              hmetric_pos.le
      _ = A := by
          field_simp [hmetric_pos.ne']
  calc
    (∑ Q' : β,
      (metric Q' ^ j *
          appendixFHoleIncompMomentKernel HF zK κ₀ 0 Q Q') /
        metric Q)
        =
      (∑ Q' : β,
        metric Q' ^ j *
          appendixFHoleIncompMomentKernel HF zK κ₀ 0 Q Q') /
        metric Q := by
          simp [Finset.sum_div]
    _ ≤ A := hdiv

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

/-- Fixed complete-tree parent kernel summand for the marked-root `H#`
recursion.

This exposes one fixed complete-tree shape before the later sum over all
complete-tree spanning trees.  It is intentionally unnormalized: each nonroot
edge carries only the hard-core moment kernel, and the root carries the marked
source weight. -/
noncomputable def appendixFHoleHsharpWeightedTreeMarkedRootFixedParentKernelSum
    {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (κ₀ : ℝ)
    (r : Cube d L)
    (n : ℕ)
    (T : Finset (Sym2 (Fin (n + 1)))) : ℝ :=
  ∑ X ∈ (Finset.univ :
      Finset (Fin (n + 1) → OmegaPolymerType HF zK)).filter
        (fun X => r ∈ skeleton HF (X 0).val),
    (∏ v ∈ Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0),
      appendixFHoleIncompMomentKernel HF zK κ₀ 0
        (X (KP.bfsParent T v)) (X v)) *
      w (X 0)

/-- The complete parent-kernel sum decomposes as the finite sum of its fixed
complete-tree summands. -/
theorem appendixFHoleHsharpWeightedTreeMarkedRootCompleteParentKernelSum_eq_sum_fixed
    {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (κ₀ : ℝ)
    (r : Cube d L)
    (n : ℕ) :
    appendixFHoleHsharpWeightedTreeMarkedRootCompleteParentKernelSum
        HF zK w κ₀ r n =
      ∑ T ∈ KP.spanningTrees (⊤ : SimpleGraph (Fin (n + 1))),
        appendixFHoleHsharpWeightedTreeMarkedRootFixedParentKernelSum
          HF zK w κ₀ r n T := by
  classical
  let all : Finset (Fin (n + 1) → OmegaPolymerType HF zK) := Finset.univ
  let marked : Finset (Fin (n + 1) → OmegaPolymerType HF zK) :=
    all.filter (fun X => r ∈ skeleton HF (X 0).val)
  let topTrees : Finset (Finset (Sym2 (Fin (n + 1)))) :=
    KP.spanningTrees (⊤ : SimpleGraph (Fin (n + 1)))
  let term
      (X : Fin (n + 1) → OmegaPolymerType HF zK)
      (T : Finset (Sym2 (Fin (n + 1)))) : ℝ :=
    (∏ v ∈ Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0),
      appendixFHoleIncompMomentKernel HF zK κ₀ 0
        (X (KP.bfsParent T v)) (X v)) *
      w (X 0)
  calc
    appendixFHoleHsharpWeightedTreeMarkedRootCompleteParentKernelSum
        HF zK w κ₀ r n
        = ∑ X ∈ marked, ∑ T ∈ topTrees, term X T := by
          simp [appendixFHoleHsharpWeightedTreeMarkedRootCompleteParentKernelSum,
            marked, all, topTrees, term]
    _ = ∑ T ∈ topTrees, ∑ X ∈ marked, term X T := by
          rw [Finset.sum_comm]
    _ =
      ∑ T ∈ topTrees,
        appendixFHoleHsharpWeightedTreeMarkedRootFixedParentKernelSum
          HF zK w κ₀ r n T := by
          simp [appendixFHoleHsharpWeightedTreeMarkedRootFixedParentKernelSum,
            marked, all, topTrees, term]

/-- Root moment left by the normalized fixed-tree kernel recursion.

The exponent is the rooted BFS child count of the root in the fixed tree
shape.  Later summability/source estimates can bound this pinned root sum;
the finite recursion below keeps it explicit. -/
noncomputable def appendixFHoleHsharpWeightedTreeMarkedRootFixedTreeRootMomentSum
    {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (r : Cube d L)
    (n : ℕ)
    (T : Finset (Sym2 (Fin (n + 1)))) : ℝ :=
  ∑ Q ∈ (Finset.univ : Finset (OmegaPolymerType HF zK)).filter
      (fun Q => r ∈ skeleton HF Q.val),
    (((discreteModifiedMetric HF Q.val + 1 : ℕ) : ℝ) ^
        KP.rootedChildCount T 0) *
      w Q

/-- Marked-root metric moment bound for source weights dominated by the spare
exponential weight.  This is the root-side companion to the normalized
child-moment budget. -/
theorem appendixFHole_markedRootMetricMomentSum_le_factorial_mul
    {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (κ₀ : ℝ)
    (r : Cube d L)
    (j : ℕ)
    (_hw : ∀ Q : OmegaPolymerType HF zK, 0 ≤ w Q)
    (hw_exp :
      ∀ Q : OmegaPolymerType HF zK,
        w Q ≤ appendixFHoleExpWeight HF (2 * κ₀) Q.val)
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
    (∑ Q ∈ (Finset.univ : Finset (OmegaPolymerType HF zK)).filter
        (fun Q => r ∈ skeleton HF Q.val),
      (((discreteModifiedMetric HF Q.val + 1 : ℕ) : ℝ) ^ j) *
        w Q)
      ≤
    (j.factorial : ℝ) *
      appendixFSecondUrsellMomentConstant d κ₀ ^ (j + 1) := by
  classical
  let Λ : Finset (OmegaPolymerType HF zK) := Finset.univ
  let f : OmegaPolymerType HF zK → ℝ := fun Q =>
    (((discreteModifiedMetric HF Q.val + 1 : ℕ) : ℝ) ^ j) * w Q
  let g : OmegaPolymerType HF zK → ℝ := fun Q =>
    (((discreteModifiedMetric HF Q.val + 1 : ℕ) : ℝ) ^ j) *
      appendixFHoleExpWeight HF (2 * κ₀) Q.val
  have hpoint : ∀ Q ∈ Λ.filter (fun Q => r ∈ skeleton HF Q.val),
      f Q ≤ g Q := by
    intro Q _hQ
    exact mul_le_mul_of_nonneg_left (hw_exp Q) (pow_nonneg (by positivity) j)
  calc
    (∑ Q ∈ (Finset.univ : Finset (OmegaPolymerType HF zK)).filter
        (fun Q => r ∈ skeleton HF Q.val),
      (((discreteModifiedMetric HF Q.val + 1 : ℕ) : ℝ) ^ j) *
        w Q)
        = ∑ Q ∈ Λ.filter (fun Q => r ∈ skeleton HF Q.val), f Q := by
          rfl
    _ ≤ ∑ Q ∈ Λ.filter (fun Q => r ∈ skeleton HF Q.val), g Q := by
          exact Finset.sum_le_sum fun Q hQ => hpoint Q hQ
    _ ≤
      (j.factorial : ℝ) *
        appendixFSecondUrsellMomentConstant d κ₀ ^ (j + 1) := by
          simpa [Λ, g] using
            appendixFHole_rootedFiniteMetricMomentExpWeightSum_le
              HF zK Λ r κ₀ j hκ₀ hdisj hnoedges hholes_ne hCq

/-- Normalized fixed-tree kernel sum for the parent-oriented `H#` recursion.

Each nonroot edge contributes the hard-core moment kernel, multiplied by the
child metric to the child's rooted child count and divided by the parent
metric.  The parent denominators are the algebraic device that will later
cancel against child powers when this normalized object is compared with the
unnormalized complete-parent kernel sum. -/
noncomputable def
    appendixFHoleHsharpWeightedTreeMarkedRootFixedTreeNormalizedKernelSum
    {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (κ₀ : ℝ)
    (r : Cube d L)
    (n : ℕ)
    (T : Finset (Sym2 (Fin (n + 1)))) : ℝ :=
  ∑ X : Fin (n + 1) → OmegaPolymerType HF zK,
    (∏ v ∈ Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0),
      ((((discreteModifiedMetric HF (X v).val + 1 : ℕ) : ℝ) ^
            KP.rootedChildCount T v) *
          appendixFHoleIncompMomentKernel HF zK κ₀ 0
            (X (KP.bfsParent T v)) (X v)) /
        (((discreteModifiedMetric HF (X (KP.bfsParent T v)).val + 1 : ℕ) : ℝ))) *
      (if r ∈ skeleton HF (X 0).val then
        (((discreteModifiedMetric HF (X 0).val + 1 : ℕ) : ℝ) ^
            KP.rootedChildCount T 0) *
          w (X 0)
      else
        0)

/-- Exact metric cancellation between the normalized fixed-tree kernel and the
unnormalized fixed-parent kernel.

The product of parent metric denominators is regrouped by BFS parent fibers;
`KP.prod_bfsParent_nonroot_eq_prod_pow_rootedChildCount` turns it into the
product of vertex metrics raised to rooted child counts, which is exactly the
nonroot child powers together with the marked root power. -/
theorem appendixFHoleHsharpWeightedTreeMarkedRootFixedParentKernelSum_eq_normalizedKernelSum
    {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (κ₀ : ℝ)
    (r : Cube d L)
    (n : ℕ)
    (T : Finset (Sym2 (Fin (n + 1)))) :
    appendixFHoleHsharpWeightedTreeMarkedRootFixedParentKernelSum
        HF zK w κ₀ r n T =
      appendixFHoleHsharpWeightedTreeMarkedRootFixedTreeNormalizedKernelSum
        HF zK w κ₀ r n T := by
  classical
  let β := OmegaPolymerType HF zK
  let all : Finset (Fin (n + 1) → β) := Finset.univ
  let marked : Finset (Fin (n + 1) → β) :=
    all.filter (fun X => r ∈ skeleton HF (X 0).val)
  let nonroot : Finset (Fin (n + 1)) :=
    Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0)
  let metric : β → ℝ := fun Q =>
    (((discreteModifiedMetric HF Q.val + 1 : ℕ) : ℝ))
  let childCount : Fin (n + 1) → ℕ := fun v => KP.rootedChildCount T v
  let kernel (X : Fin (n + 1) → β) (v : Fin (n + 1)) : ℝ :=
    appendixFHoleIncompMomentKernel HF zK κ₀ 0
      (X (KP.bfsParent T v)) (X v)
  have hcancel : ∀ X : Fin (n + 1) → β,
      (∏ v ∈ nonroot,
        (metric (X v) ^ childCount v * kernel X v) /
          metric (X (KP.bfsParent T v))) *
        (metric (X 0) ^ childCount 0 * w (X 0)) =
      (∏ v ∈ nonroot, kernel X v) * w (X 0) := by
    intro X
    have hparent :
        (∏ v ∈ nonroot, metric (X (KP.bfsParent T v))) =
          ∏ v : Fin (n + 1), metric (X v) ^ childCount v := by
      simpa [nonroot, metric, childCount] using
        KP.prod_bfsParent_nonroot_eq_prod_pow_rootedChildCount
          (T := T) (f := fun v : Fin (n + 1) => metric (X v))
    have hmetric :
        (∏ v ∈ nonroot, metric (X v) ^ childCount v) *
            metric (X 0) ^ childCount 0 =
          ∏ v : Fin (n + 1), metric (X v) ^ childCount v := by
      dsimp [nonroot]
      rw [Finset.filter_ne',
        ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ 0)]
      ring
    have hden_ne :
        (∏ v ∈ nonroot, metric (X (KP.bfsParent T v))) ≠ 0 := by
      positivity
    have hnonroot_metric_ne :
        (∏ v ∈ nonroot, metric (X v) ^ childCount v) ≠ 0 := by
      positivity
    have hroot_metric_ne :
        metric (X 0) ^ childCount 0 ≠ 0 := by
      positivity
    calc
      (∏ v ∈ nonroot,
        (metric (X v) ^ childCount v * kernel X v) /
          metric (X (KP.bfsParent T v))) *
        (metric (X 0) ^ childCount 0 * w (X 0))
          =
        (((∏ v ∈ nonroot, metric (X v) ^ childCount v) *
              (∏ v ∈ nonroot, kernel X v)) /
            (∏ v ∈ nonroot, metric (X (KP.bfsParent T v)))) *
          (metric (X 0) ^ childCount 0 * w (X 0)) := by
            simp [Finset.prod_div_distrib, Finset.prod_mul_distrib,
              mul_assoc, mul_comm]
      _ =
        (∏ v ∈ nonroot, kernel X v) * w (X 0) := by
          rw [hparent, ← hmetric]
          field_simp [hnonroot_metric_ne, hroot_metric_ne]
  calc
    appendixFHoleHsharpWeightedTreeMarkedRootFixedParentKernelSum
        HF zK w κ₀ r n T
        =
      ∑ X ∈ marked,
        (∏ v ∈ nonroot, kernel X v) * w (X 0) := by
          simp [appendixFHoleHsharpWeightedTreeMarkedRootFixedParentKernelSum,
            marked, all, nonroot, kernel, β]
    _ =
      ∑ X ∈ marked,
        (∏ v ∈ nonroot,
          (metric (X v) ^ childCount v * kernel X v) /
            metric (X (KP.bfsParent T v))) *
          (metric (X 0) ^ childCount 0 * w (X 0)) := by
          refine Finset.sum_congr rfl fun X _hX => ?_
          exact (hcancel X).symm
    _ =
      appendixFHoleHsharpWeightedTreeMarkedRootFixedTreeNormalizedKernelSum
        HF zK w κ₀ r n T := by
          let p : (Fin (n + 1) → β) → Prop := fun X =>
            r ∈ skeleton HF (X 0).val
          let f : (Fin (n + 1) → β) → ℝ := fun X =>
            (∏ v ∈ nonroot,
              (metric (X v) ^ childCount v * kernel X v) /
                metric (X (KP.bfsParent T v))) *
              (metric (X 0) ^ childCount 0 * w (X 0))
          calc
            (∑ X ∈ marked,
              (∏ v ∈ nonroot,
                (metric (X v) ^ childCount v * kernel X v) /
                  metric (X (KP.bfsParent T v))) *
                (metric (X 0) ^ childCount 0 * w (X 0)))
                = ∑ X ∈ all.filter p, f X := by
                  rfl
            _ = ∑ X ∈ all, if p X then f X else 0 := by
                  simpa using
                    (Finset.sum_filter (s := all) (p := p) (f := f))
            _ =
              appendixFHoleHsharpWeightedTreeMarkedRootFixedTreeNormalizedKernelSum
                HF zK w κ₀ r n T := by
                simp [appendixFHoleHsharpWeightedTreeMarkedRootFixedTreeNormalizedKernelSum,
                  all, nonroot, metric, childCount, kernel, p, f, β]

/-- Generic fixed-tree normalized kernel adapter.

For a fixed complete-tree shape, the vertexwise walk bound consumes any
per-vertex normalized child budget `A v`, leaving only the pinned root metric
moment.  The concrete hard-core factorial estimate below is one specialization
of this adapter. -/
theorem
    appendixFHoleHsharpWeightedTreeMarkedRootFixedTreeNormalizedKernelSum_le_of_vertexwise_walk_budget
    {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (κ₀ : ℝ)
    (r : Cube d L)
    (n : ℕ)
    (T : Finset (Sym2 (Fin (n + 1))))
    (A : Fin (n + 1) → ℝ)
    (hT : T ∈ KP.spanningTrees (⊤ : SimpleGraph (Fin (n + 1))))
    (hw : ∀ Q : OmegaPolymerType HF zK, 0 ≤ w Q)
    (hA : ∀ v, v ≠ 0 → 0 ≤ A v)
    (hstep :
      ∀ v, v ≠ 0 → ∀ Q : OmegaPolymerType HF zK,
        (∑ Q' : OmegaPolymerType HF zK,
          ((((discreteModifiedMetric HF Q'.val + 1 : ℕ) : ℝ) ^
                KP.rootedChildCount T v) *
              appendixFHoleIncompMomentKernel HF zK κ₀ 0 Q Q') /
            (((discreteModifiedMetric HF Q.val + 1 : ℕ) : ℝ)))
          ≤ A v) :
    appendixFHoleHsharpWeightedTreeMarkedRootFixedTreeNormalizedKernelSum
        HF zK w κ₀ r n T
      ≤
    (∏ v ∈ Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0), A v) *
      appendixFHoleHsharpWeightedTreeMarkedRootFixedTreeRootMomentSum
        HF zK w r n T := by
  classical
  let β := OmegaPolymerType HF zK
  let metric : β → ℝ := fun Q =>
    (((discreteModifiedMetric HF Q.val + 1 : ℕ) : ℝ))
  let childCount : Fin (n + 1) → ℕ := fun v => KP.rootedChildCount T v
  let I : Fin (n + 1) → β → β → ℝ := fun v Q Q' =>
    (metric Q' ^ childCount v *
        appendixFHoleIncompMomentKernel HF zK κ₀ 0 Q Q') / metric Q
  let wroot : β → ℝ := fun Q =>
    if r ∈ skeleton HF Q.val then metric Q ^ childCount 0 * w Q else 0
  have htree := KP.isTree_of_mem_spanningTrees
    (⊤ : SimpleGraph (Fin (n + 1))) hT
  have hconn := htree.isConnected
  have hcard : Fintype.card (Fin (n + 1)) = n + 1 := by
    simp
  have hdesc :
      ∀ v : Fin (n + 1), v ≠ 0 →
        KP.bfsLevel T (KP.bfsParent T v) < KP.bfsLevel T v := by
    intro v hv
    have hspec := (KP.bfsParent_spec hconn hv).2
    omega
  have hI_nonneg : ∀ v Q Q', 0 ≤ I v Q Q' := by
    intro v Q Q'
    have hmetric : 0 ≤ metric Q := by positivity
    have hnum :
        0 ≤ metric Q' ^ childCount v *
          appendixFHoleIncompMomentKernel HF zK κ₀ 0 Q Q' := by
      exact mul_nonneg (pow_nonneg (by positivity) _)
        (appendixFHoleIncompMomentKernel_nonneg HF zK κ₀ 0 Q Q')
    exact div_nonneg hnum hmetric
  have hwroot_nonneg : ∀ Q, 0 ≤ wroot Q := by
    intro Q
    by_cases hmark : r ∈ skeleton HF Q.val
    · dsimp [wroot]
      rw [if_pos hmark]
      exact mul_nonneg (pow_nonneg (by positivity) _) (hw Q)
    · simp [wroot, hmark]
  have hsum : ∀ v, v ≠ 0 → ∀ Q : β, ∑ Q' : β, I v Q Q' ≤ A v := by
    intro v hv Q
    simpa [I, metric, childCount, Finset.sum_div] using hstep v hv Q
  have hwalk :=
    KP.tree_walk_bound_vertexwise n (Fin (n + 1)) β 0 (KP.bfsParent T)
      (KP.bfsLevel T) I wroot A hcard hdesc hI_nonneg hwroot_nonneg
      hA hsum
  have hroot :
      (∑ Q : β, wroot Q) =
        appendixFHoleHsharpWeightedTreeMarkedRootFixedTreeRootMomentSum
          HF zK w r n T := by
    let p : β → Prop := fun Q => r ∈ skeleton HF Q.val
    let f : β → ℝ := fun Q => metric Q ^ childCount 0 * w Q
    calc
      (∑ Q : β, wroot Q)
          = ∑ Q : β, if p Q then f Q else 0 := by
              simp [wroot, p, f]
      _ = ∑ Q ∈ (Finset.univ : Finset β).filter p, f Q := by
              simpa using
                (Finset.sum_filter
                  (s := (Finset.univ : Finset β)) (p := p) (f := f)).symm
      _ =
          appendixFHoleHsharpWeightedTreeMarkedRootFixedTreeRootMomentSum
            HF zK w r n T := by
              rfl
  have hwalk' := hwalk
  rw [hroot] at hwalk'
  simpa [appendixFHoleHsharpWeightedTreeMarkedRootFixedTreeNormalizedKernelSum,
    I, wroot, metric, childCount] using hwalk'

/-- Fixed-tree adapter for the unnormalized parent-kernel summand.

The exact metric cancellation transfers the unnormalized fixed-parent sum to
the normalized fixed-tree walk, and the generic vertexwise adapter then
consumes the local child budgets. -/
theorem appendixFHoleHsharpWeightedTreeMarkedRootFixedParentKernelSum_le_of_vertexwise_walk_budget
    {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (κ₀ : ℝ)
    (r : Cube d L)
    (n : ℕ)
    (T : Finset (Sym2 (Fin (n + 1))))
    (A : Fin (n + 1) → ℝ)
    (hT : T ∈ KP.spanningTrees (⊤ : SimpleGraph (Fin (n + 1))))
    (hw : ∀ Q : OmegaPolymerType HF zK, 0 ≤ w Q)
    (hA : ∀ v, v ≠ 0 → 0 ≤ A v)
    (hstep :
      ∀ v, v ≠ 0 → ∀ Q : OmegaPolymerType HF zK,
        (∑ Q' : OmegaPolymerType HF zK,
          ((((discreteModifiedMetric HF Q'.val + 1 : ℕ) : ℝ) ^
                KP.rootedChildCount T v) *
              appendixFHoleIncompMomentKernel HF zK κ₀ 0 Q Q') /
            (((discreteModifiedMetric HF Q.val + 1 : ℕ) : ℝ)))
          ≤ A v) :
    appendixFHoleHsharpWeightedTreeMarkedRootFixedParentKernelSum
        HF zK w κ₀ r n T
      ≤
    (∏ v ∈ Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0), A v) *
      appendixFHoleHsharpWeightedTreeMarkedRootFixedTreeRootMomentSum
        HF zK w r n T := by
  rw [appendixFHoleHsharpWeightedTreeMarkedRootFixedParentKernelSum_eq_normalizedKernelSum]
  exact
    appendixFHoleHsharpWeightedTreeMarkedRootFixedTreeNormalizedKernelSum_le_of_vertexwise_walk_budget
      HF zK w κ₀ r n T A hT hw hA hstep

/-- Fixed-tree normalized kernel recursion.

For a fixed complete-tree shape, the vertexwise walk bound and the hard-core
moment estimate give independent child budgets
`childCount(v)! * C^(childCount(v)+1)`, leaving only the pinned root moment
sum.  This is the finite moment-budget step needed before the later
cancellation back to the unnormalized complete-parent kernel sum. -/
theorem appendixFHoleHsharpWeightedTreeMarkedRootFixedTreeNormalizedKernelSum_le_momentBudget
    {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (κ₀ : ℝ)
    (r : Cube d L)
    (n : ℕ)
    (T : Finset (Sym2 (Fin (n + 1))))
    (hT : T ∈ KP.spanningTrees (⊤ : SimpleGraph (Fin (n + 1))))
    (hw : ∀ Q : OmegaPolymerType HF zK, 0 ≤ w Q)
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
    appendixFHoleHsharpWeightedTreeMarkedRootFixedTreeNormalizedKernelSum
        HF zK w κ₀ r n T ≤
      (∏ v ∈ Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0),
        ((KP.rootedChildCount T v).factorial : ℝ) *
          appendixFSecondUrsellMomentConstant d κ₀ ^
            (KP.rootedChildCount T v + 1)) *
        appendixFHoleHsharpWeightedTreeMarkedRootFixedTreeRootMomentSum
          HF zK w r n T := by
  classical
  let childCount : Fin (n + 1) → ℕ := fun v => KP.rootedChildCount T v
  let C : ℝ := appendixFSecondUrsellMomentConstant d κ₀
  let A : Fin (n + 1) → ℝ := fun v =>
    ((childCount v).factorial : ℝ) * C ^ (childCount v + 1)
  have hC_nonneg : 0 ≤ C := by
    have hC_one : 1 ≤ C := by
      exact le_max_left _ _
    exact (zero_le_one).trans hC_one
  have hA_nonneg : ∀ v, v ≠ 0 → 0 ≤ A v := by
    intro v _hv
    exact mul_nonneg (by positivity) (pow_nonneg hC_nonneg _)
  have hstep :
      ∀ v, v ≠ 0 → ∀ Q : OmegaPolymerType HF zK,
        (∑ Q' : OmegaPolymerType HF zK,
          ((((discreteModifiedMetric HF Q'.val + 1 : ℕ) : ℝ) ^
                KP.rootedChildCount T v) *
              appendixFHoleIncompMomentKernel HF zK κ₀ 0 Q Q') /
            (((discreteModifiedMetric HF Q.val + 1 : ℕ) : ℝ)))
          ≤ A v := by
    intro v _hv Q
    simpa [A, C, childCount] using
      appendixFHoleIncompMomentKernel_normalizedChildMoment_sum_le_factorial_mul
        HF zK Q κ₀ (childCount v) hκ₀ hdisj hnoedges hholes_ne hCq
  simpa [A, C, childCount] using
    appendixFHoleHsharpWeightedTreeMarkedRootFixedTreeNormalizedKernelSum_le_of_vertexwise_walk_budget
      HF zK w κ₀ r n T A hT hw hA_nonneg hstep

/-- Closed ratio for the finite second-Ursell leaf summation after summing
complete-tree shapes.  The factor `4` is purely combinatorial; the moment
constant itself does not contain it. -/
noncomputable def appendixFSecondUrsellLeafConstant
    (d : ℕ) (κ₀ : ℝ) : ℝ :=
  4 * appendixFSecondUrsellMomentConstant d κ₀ ^ 2

/-- Concrete fixed-parent child-moment bound before summing the marked root.

This is the fixed-tree adapter with the normalized child budgets instantiated
by the finite hard-core moment estimate. -/
theorem
    appendixFHoleHsharpWeightedTreeMarkedRootFixedParentKernelSum_le_prod_childMomentBudget_mul_rootMoment
    {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (κ₀ : ℝ)
    (r : Cube d L)
    (n : ℕ)
    (T : Finset (Sym2 (Fin (n + 1))))
    (hT : T ∈ KP.spanningTrees (⊤ : SimpleGraph (Fin (n + 1))))
    (hw : ∀ Q : OmegaPolymerType HF zK, 0 ≤ w Q)
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
    appendixFHoleHsharpWeightedTreeMarkedRootFixedParentKernelSum
        HF zK w κ₀ r n T ≤
      (∏ v ∈ Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0),
        ((KP.rootedChildCount T v).factorial : ℝ) *
          appendixFSecondUrsellMomentConstant d κ₀ ^
            (KP.rootedChildCount T v + 1)) *
        appendixFHoleHsharpWeightedTreeMarkedRootFixedTreeRootMomentSum
          HF zK w r n T := by
  rw [appendixFHoleHsharpWeightedTreeMarkedRootFixedParentKernelSum_eq_normalizedKernelSum]
  exact
    appendixFHoleHsharpWeightedTreeMarkedRootFixedTreeNormalizedKernelSum_le_momentBudget
      HF zK w κ₀ r n T hT hw hκ₀ hdisj hnoedges hholes_ne hCq

/-- Fixed-tree `H#` parent-kernel bound after summing the marked root.

For one complete-tree shape, all finite child and root metric moments close to
the child-factorial product times the exact moment power `M^(2n+1)`. -/
theorem
    appendixFHoleHsharpWeightedTreeMarkedRootFixedParentKernelSum_le_childFactor_mul_momentPow
    {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (κ₀ : ℝ)
    (r : Cube d L)
    (n : ℕ)
    (T : Finset (Sym2 (Fin (n + 1))))
    (hT : T ∈ KP.spanningTrees (⊤ : SimpleGraph (Fin (n + 1))))
    (hw : ∀ Q : OmegaPolymerType HF zK, 0 ≤ w Q)
    (hw_exp :
      ∀ Q : OmegaPolymerType HF zK,
        w Q ≤ appendixFHoleExpWeight HF (2 * κ₀) Q.val)
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
    appendixFHoleHsharpWeightedTreeMarkedRootFixedParentKernelSum
        HF zK w κ₀ r n T
      ≤
    (∏ v : Fin (n + 1),
      ((KP.rootedChildCount T v).factorial : ℝ)) *
      appendixFSecondUrsellMomentConstant d κ₀ ^ (2 * n + 1) := by
  classical
  let nonroot : Finset (Fin (n + 1)) :=
    Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0)
  let c : Fin (n + 1) → ℕ := fun v => KP.rootedChildCount T v
  let M : ℝ := appendixFSecondUrsellMomentConstant d κ₀
  have hfixed :=
    appendixFHoleHsharpWeightedTreeMarkedRootFixedParentKernelSum_le_prod_childMomentBudget_mul_rootMoment
      HF zK w κ₀ r n T hT hw hκ₀ hdisj hnoedges hholes_ne hCq
  have hroot :
      appendixFHoleHsharpWeightedTreeMarkedRootFixedTreeRootMomentSum
          HF zK w r n T
        ≤ ((c 0).factorial : ℝ) * M ^ (c 0 + 1) := by
    simpa [appendixFHoleHsharpWeightedTreeMarkedRootFixedTreeRootMomentSum,
      c, M] using
      appendixFHole_markedRootMetricMomentSum_le_factorial_mul
        HF zK w κ₀ r (c 0) hw hw_exp hκ₀ hdisj hnoedges hholes_ne hCq
  have hM_nonneg : 0 ≤ M := by
    simpa [M] using appendixFSecondUrsellMomentConstant_nonneg d κ₀
  have hchild_nonneg :
      0 ≤ ∏ v ∈ nonroot,
        ((c v).factorial : ℝ) * M ^ (c v + 1) := by
    exact Finset.prod_nonneg fun v _hv =>
      mul_nonneg (by positivity) (pow_nonneg hM_nonneg _)
  have hbounded :
      appendixFHoleHsharpWeightedTreeMarkedRootFixedParentKernelSum
          HF zK w κ₀ r n T
        ≤
      (∏ v ∈ nonroot,
        ((c v).factorial : ℝ) * M ^ (c v + 1)) *
        (((c 0).factorial : ℝ) * M ^ (c 0 + 1)) := by
    refine hfixed.trans ?_
    exact mul_le_mul_of_nonneg_left hroot hchild_nonneg
  have hfactor_split :
      (∏ v ∈ nonroot, ((c v).factorial : ℝ)) *
          ((c 0).factorial : ℝ)
        =
      ∏ v : Fin (n + 1), ((c v).factorial : ℝ) := by
    dsimp [nonroot]
    rw [Finset.filter_ne',
      ← Finset.mul_prod_erase Finset.univ
        (fun v : Fin (n + 1) => ((c v).factorial : ℝ))
        (Finset.mem_univ 0)]
    ring
  have hpow_split :
      (∏ v ∈ nonroot, M ^ (c v + 1)) * M ^ (c 0 + 1)
        =
      ∏ v : Fin (n + 1), M ^ (c v + 1) := by
    dsimp [nonroot]
    rw [Finset.filter_ne',
      ← Finset.mul_prod_erase Finset.univ
        (fun v : Fin (n + 1) => M ^ (c v + 1))
        (Finset.mem_univ 0)]
    ring
  have hsum_exp :
      (∑ v : Fin (n + 1), (c v + 1)) = 2 * n + 1 := by
    have hsum_c : (∑ v : Fin (n + 1), c v) = n := by
      simpa [c] using KP.sum_rootedChildCount_eq (T := T)
    rw [Finset.sum_add_distrib, hsum_c]
    simp [Fintype.card_fin]
    omega
  have hpow_all :
      (∏ v : Fin (n + 1), M ^ (c v + 1)) =
        M ^ (2 * n + 1) := by
    calc
      (∏ v : Fin (n + 1), M ^ (c v + 1))
          = M ^ (∑ v : Fin (n + 1), (c v + 1)) := by
            rw [Finset.prod_pow_eq_pow_sum]
      _ = M ^ (2 * n + 1) := by
            rw [hsum_exp]
  have hbudget :
      (∏ v ∈ nonroot,
        ((c v).factorial : ℝ) * M ^ (c v + 1)) *
        (((c 0).factorial : ℝ) * M ^ (c 0 + 1))
        =
      (∏ v : Fin (n + 1), ((c v).factorial : ℝ)) *
        M ^ (2 * n + 1) := by
    rw [Finset.prod_mul_distrib]
    calc
      ((∏ v ∈ nonroot, ((c v).factorial : ℝ)) *
          (∏ v ∈ nonroot, M ^ (c v + 1))) *
          (((c 0).factorial : ℝ) * M ^ (c 0 + 1))
          =
        ((∏ v ∈ nonroot, ((c v).factorial : ℝ)) *
            ((c 0).factorial : ℝ)) *
          ((∏ v ∈ nonroot, M ^ (c v + 1)) * M ^ (c 0 + 1)) := by
            ring
      _ =
        (∏ v : Fin (n + 1), ((c v).factorial : ℝ)) *
          M ^ (2 * n + 1) := by
            rw [hfactor_split, hpow_split, hpow_all]
  exact hbounded.trans_eq hbudget

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

/-- Marked-root `H#` leaf summation with the closed finite geometric ratio.

This is the aggregate finite theorem: the raw marked-root tree sum is
overcounted by complete-tree parent kernels, each fixed tree is bounded by the
child-factorial moment power, and the complete-tree shapes are summed by the
rooted child-count `4^n` theorem. -/
theorem appendixFHoleHsharpWeightedTreeMarkedRootSum_le_geometric_of_expWeight
    {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (r : Cube d L)
    (n : ℕ)
    (κ₀ : ℝ)
    (hκ₀ : 0 < κ₀)
    (hw : ∀ Q : OmegaPolymerType HF zK, 0 ≤ w Q)
    (hw_exp :
      ∀ Q : OmegaPolymerType HF zK,
        w Q ≤ appendixFHoleExpWeight HF (2 * κ₀) Q.val)
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne : ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1) :
    ((n : ℝ) + 1) *
        appendixFHoleHsharpWeightedTreeMarkedRootSum
          HF zK w r n
      ≤
    appendixFSecondUrsellMomentConstant d κ₀ *
      appendixFSecondUrsellLeafConstant d κ₀ ^ n := by
  classical
  let topTrees : Finset (Finset (Sym2 (Fin (n + 1)))) :=
    KP.spanningTrees (⊤ : SimpleGraph (Fin (n + 1)))
  let M : ℝ := appendixFSecondUrsellMomentConstant d κ₀
  let norm : ℝ := ((n : ℝ) + 1) * (((n + 1).factorial : ℝ))⁻¹
  let S : ℝ :=
    ∑ T ∈ topTrees,
      ∏ v : Fin (n + 1), ((KP.rootedChildCount T v).factorial : ℝ)
  have hM_nonneg : 0 ≤ M := by
    simpa [M] using appendixFSecondUrsellMomentConstant_nonneg d κ₀
  have hnorm_nonneg : 0 ≤ norm := by
    dsimp [norm]
    positivity
  have hraw_kernel :
      appendixFHoleHsharpWeightedTreeMarkedRootRawSum HF zK w r n
        ≤
      appendixFHoleHsharpWeightedTreeMarkedRootCompleteParentKernelSum
        HF zK w κ₀ r n := by
    exact
      (appendixFHoleHsharpWeightedTreeMarkedRootRawSum_le_completeTreeParentSum
        HF zK w r n hw).trans
        (appendixFHoleHsharpWeightedTreeMarkedRootCompleteParentSum_le_kernelSum
          HF zK w κ₀ r n hw hw_exp)
  have hkernel :
      appendixFHoleHsharpWeightedTreeMarkedRootCompleteParentKernelSum
          HF zK w κ₀ r n
        ≤
      ∑ T ∈ topTrees,
        (∏ v : Fin (n + 1),
          ((KP.rootedChildCount T v).factorial : ℝ)) *
          M ^ (2 * n + 1) := by
    calc
      appendixFHoleHsharpWeightedTreeMarkedRootCompleteParentKernelSum
          HF zK w κ₀ r n
          =
        ∑ T ∈ topTrees,
          appendixFHoleHsharpWeightedTreeMarkedRootFixedParentKernelSum
            HF zK w κ₀ r n T := by
            simpa [topTrees] using
              appendixFHoleHsharpWeightedTreeMarkedRootCompleteParentKernelSum_eq_sum_fixed
                HF zK w κ₀ r n
      _ ≤
        ∑ T ∈ topTrees,
          (∏ v : Fin (n + 1),
            ((KP.rootedChildCount T v).factorial : ℝ)) *
            M ^ (2 * n + 1) := by
            refine Finset.sum_le_sum ?_
            intro T hT
            simpa [M] using
              appendixFHoleHsharpWeightedTreeMarkedRootFixedParentKernelSum_le_childFactor_mul_momentPow
                HF zK w κ₀ r n T hT hw hw_exp hκ₀ hdisj hnoedges
                hholes_ne hCq
  have htree_sum : norm * S ≤ (4 : ℝ) ^ n := by
    simpa [norm, S, topTrees] using
      KP.rootedChildCount_factorialTreeSum_normalized_le_four_pow n
  have hsum_const :
      (∑ T ∈ topTrees,
        (∏ v : Fin (n + 1),
          ((KP.rootedChildCount T v).factorial : ℝ)) *
          M ^ (2 * n + 1))
        = S * M ^ (2 * n + 1) := by
    dsimp [S]
    rw [Finset.sum_mul]
  calc
    ((n : ℝ) + 1) *
        appendixFHoleHsharpWeightedTreeMarkedRootSum
          HF zK w r n
        =
      norm * appendixFHoleHsharpWeightedTreeMarkedRootRawSum HF zK w r n := by
        rw [appendixFHoleHsharpWeightedTreeMarkedRootSum_eq_inv_factorial_mul_rawSum]
        simp [norm]
        ring
    _ ≤
      norm *
        appendixFHoleHsharpWeightedTreeMarkedRootCompleteParentKernelSum
          HF zK w κ₀ r n := by
        exact mul_le_mul_of_nonneg_left hraw_kernel hnorm_nonneg
    _ ≤
      norm *
        (∑ T ∈ topTrees,
          (∏ v : Fin (n + 1),
            ((KP.rootedChildCount T v).factorial : ℝ)) *
            M ^ (2 * n + 1)) := by
        exact mul_le_mul_of_nonneg_left hkernel hnorm_nonneg
    _ =
      M ^ (2 * n + 1) * (norm * S) := by
        rw [hsum_const]
        ring
    _ ≤ M ^ (2 * n + 1) * (4 : ℝ) ^ n := by
        exact mul_le_mul_of_nonneg_left htree_sum (pow_nonneg hM_nonneg _)
    _ =
      appendixFSecondUrsellMomentConstant d κ₀ *
        appendixFSecondUrsellLeafConstant d κ₀ ^ n := by
        simp [appendixFSecondUrsellLeafConstant, M]
        ring_nf

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

/-- Direct target-decaying weighted-tree bound from the finite leaf summation.

The target exponential is extracted first, then the new marked-root geometric
leaf bound supplies `Croot = M` and `Cleaf = 4*M^2`. -/
theorem appendixFHoleHsharpWeightedTreeTerm_le_geometric_of_expWeight_leafSummation
    {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w u : OmegaPolymerType HF zK → ℝ)
    (Y : Finset (Cube d L))
    (r : Cube d L)
    (n : ℕ)
    (rate κ₀ : ℝ)
    (hrate : 0 ≤ rate)
    (hw : ∀ Q : OmegaPolymerType HF zK, 0 ≤ w Q)
    (hu : ∀ Q : OmegaPolymerType HF zK, 0 ≤ u Q)
    (hsplit :
      ∀ Q : OmegaPolymerType HF zK,
        w Q ≤ appendixFHoleExpWeight HF rate Q.val * u Q)
    (hu_exp :
      ∀ Q : OmegaPolymerType HF zK,
        u Q ≤ appendixFHoleExpWeight HF (2 * κ₀) Q.val)
    (hr : r ∈ skeleton HF Y)
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
    appendixFHoleHsharpWeightedTreeTerm HF zK w Y n ≤
      appendixFSecondUrsellMomentConstant d κ₀ *
        appendixFHoleExpWeight HF rate Y *
        appendixFSecondUrsellLeafConstant d κ₀ ^ n := by
  exact
    appendixFHoleHsharpWeightedTreeTerm_le_geometric_of_markedRootLeafSummation
      HF zK w u Y r n rate
      (appendixFSecondUrsellMomentConstant d κ₀)
      (appendixFSecondUrsellLeafConstant d κ₀)
      hrate hw hu hsplit hr
      (appendixFHoleHsharpWeightedTreeMarkedRootSum_le_geometric_of_expWeight
        HF zK u r n κ₀ hκ₀ hu hu_exp hdisj hnoedges hholes_ne hCq)

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
