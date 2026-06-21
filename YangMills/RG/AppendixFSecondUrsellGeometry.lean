/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFQuantitative
import YangMills.RG.AppendixFLocalSummability
import YangMills.RG.AppendixFSecondUrsellWeightedTree
import YangMills.KP.PenrosePrep

/-!
# Appendix F second-Ursell geometry

This module starts the finite geometric layer needed after the source-facing
tree majorant for the second Appendix-F Ursell expansion.  It proves that a
KP spanning tree in the source-facing `Ω`-active polymer incompatibility graph
controls the modified metric of the full target union by the sum of the
shifted modified metrics of its leaves.

No source estimate, summability constant, or analytic Appendix-F inequality is
introduced here.  The theorem below is pure finite geometry.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

attribute [local instance] Classical.propDecidable

open Finset
open scoped BigOperators

namespace YangMills.RG

/-- The rooted modified-metric geometric constant used when summing finite
with-holes polymers through a prescribed active skeleton cube. -/
noncomputable def appendixFHoleRootSumConstant (d : ℕ) (κ₀ : ℝ) : ℝ :=
  (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
    (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)))⁻¹

/-- A KP spanning tree for the `Ω`-active with-holes polymer system stitches
minimal modified-metric spanning sets for the leaves into one connected
spanning set for the full cluster union.  Consequently the shifted modified
metric of the union is bounded by the sum of shifted leaf metrics.

This is the tree-indexed form of the finite metric part of Dimock Appendix F
for the second Ursell layer; it is intentionally independent of all activity
size and summability hypotheses. -/
theorem omegaClusterUnion_discreteModifiedMetric_add_one_le_sum_of_spanningTree
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    {n : ℕ} (X : Fin (n + 1) → OmegaPolymerType HF zK)
    {T : Finset (Sym2 (Fin (n + 1)))}
    (hT : T ∈ KP.spanningTrees
      (KP.incompGraph (omegaHolePolymerSystem HF zK) X)) :
    ((discreteModifiedMetric HF (omegaClusterUnion HF zK X) + 1 : ℕ) : ℝ)
      ≤ ∑ i : Fin (n + 1),
          ((discreteModifiedMetric HF (X i).val + 1 : ℕ) : ℝ) := by
  classical
  let root : Fin (n + 1) → Cube d L := fun i =>
    Classical.choose (X i).property.right.right.right
  have hroot : ∀ i : Fin (n + 1), root i ∈ skeleton HF (X i).val := by
    intro i
    exact Classical.choose_spec (X i).property.right.right.right
  let S : Fin (n + 1) → Finset (Cube d L) := fun i =>
    Classical.choose
      (exists_minimal_spanning_set HF (X i).val (root i) (hroot i)
        (X i).property.right.left)
  have hS_skel : ∀ i : Fin (n + 1), skeleton HF (X i).val ⊆ S i := by
    intro i
    exact (Classical.choose_spec
      (exists_minimal_spanning_set HF (X i).val (root i) (hroot i)
        (X i).property.right.left)).1
  have hS_sub : ∀ i : Fin (n + 1), S i ⊆ (X i).val := by
    intro i
    exact (Classical.choose_spec
      (exists_minimal_spanning_set HF (X i).val (root i) (hroot i)
        (X i).property.right.left)).2.1
  have hS_conn : ∀ i : Fin (n + 1), cubeConnected (S i) := by
    intro i
    exact (Classical.choose_spec
      (exists_minimal_spanning_set HF (X i).val (root i) (hroot i)
        (X i).property.right.left)).2.2.1
  have hS_card :
      ∀ i : Fin (n + 1),
        (S i).card = discreteModifiedMetric HF (X i).val + 1 := by
    intro i
    exact (Classical.choose_spec
      (exists_minimal_spanning_set HF (X i).val (root i) (hroot i)
        (X i).property.right.left)).2.2.2.2
  have hSUnion_skel :
      skeleton HF (omegaClusterUnion HF zK X) ⊆
        (Finset.univ : Finset (Fin (n + 1))).biUnion S := by
    intro r hr
    rw [omegaClusterUnion_skeleton] at hr
    rw [Finset.mem_biUnion] at hr ⊢
    rcases hr with ⟨i, hi, hri⟩
    exact ⟨i, hi, hS_skel i hri⟩
  have hSUnion_sub :
      (Finset.univ : Finset (Fin (n + 1))).biUnion S ⊆
        omegaClusterUnion HF zK X := by
    intro r hr
    rw [Finset.mem_biUnion] at hr
    dsimp [omegaClusterUnion]
    rw [Finset.mem_biUnion]
    rcases hr with ⟨i, hi, hri⟩
    exact ⟨i, hi, hS_sub i hri⟩
  let Gtree : SimpleGraph (Fin (n + 1)) :=
    SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin (n + 1))))
  have htree_conn : Gtree.Connected :=
    (KP.isTree_of_mem_spanningTrees
      (KP.incompGraph (omegaHolePolymerSystem HF zK) X) hT).isConnected
  have hTsub :
      T ⊆ (KP.incompGraph (omegaHolePolymerSystem HF zK) X).edgeFinset :=
    KP.spanningTrees_subset
      (KP.incompGraph (omegaHolePolymerSystem HF zK) X) hT
  have hS_hadj :
      ∀ i j : Fin (n + 1), Gtree.Adj i j → ¬ Disjoint (S i) (S j) := by
    intro i j hij hdisj
    rw [SimpleGraph.fromEdgeSet_adj] at hij
    have hmemEdge :
        s(i, j) ∈
          (KP.incompGraph (omegaHolePolymerSystem HF zK) X).edgeFinset :=
      hTsub (Finset.mem_coe.mp hij.1)
    have hGadj :
        (KP.incompGraph (omegaHolePolymerSystem HF zK) X).Adj i j := by
      rwa [SimpleGraph.mem_edgeFinset] at hmemEdge
    have hinc :
        (omegaHolePolymerSystem HF zK).incomp (X i) (X j) :=
      ((KP.incompGraph_adj (omegaHolePolymerSystem HF zK) X i j).mp hGadj).2
    rcases (omegaHolePolymerSystem_incomp_iff_exists HF zK (X i) (X j)).mp
        hinc with ⟨r, hri, hrj⟩
    exact (Finset.disjoint_left.mp hdisj (hS_skel i hri)) (hS_skel j hrj)
  have hSUnion_conn :
      cubeConnected ((Finset.univ : Finset (Fin (n + 1))).biUnion S) := by
    rw [cubeConnected]
    intro x hx y hy
    rw [Finset.mem_biUnion] at hx hy
    rcases hx with ⟨i, _hi, hxi⟩
    rcases hy with ⟨j, _hj, hyj⟩
    obtain ⟨w⟩ := htree_conn.preconnected i j
    obtain ⟨wCube, hwCube⟩ :=
      walk_union_connected Gtree (cubeAdj d L) S hS_conn hS_hadj
        w x hxi y hyj
    refine ⟨wCube, ?_⟩
    intro v hv
    rcases hwCube v hv with ⟨k, _hkw, hvk⟩
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, hvk⟩
  have hskel_ne :
      (skeleton HF (omegaClusterUnion HF zK X)).Nonempty := by
    rw [omegaClusterUnion_skeleton]
    rcases (X 0).property.right.right.right with ⟨r, hr⟩
    exact ⟨r, Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ 0, hr⟩⟩
  have hmetric :
      discreteModifiedMetric HF (omegaClusterUnion HF zK X) + 1
        ≤ ((Finset.univ : Finset (Fin (n + 1))).biUnion S).card :=
    discreteModifiedMetric_add_one_le_card_of_spanning_set HF
      (omegaClusterUnion HF zK X)
      ((Finset.univ : Finset (Fin (n + 1))).biUnion S)
      hskel_ne hSUnion_skel hSUnion_sub hSUnion_conn
  have hcard :
      ((Finset.univ : Finset (Fin (n + 1))).biUnion S).card
        ≤ ∑ i : Fin (n + 1), (S i).card := by
    simpa using
      (Finset.card_biUnion_le :
        ((Finset.univ : Finset (Fin (n + 1))).biUnion S).card
          ≤ ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))), (S i).card)
  have hsum :
      (∑ i : Fin (n + 1), (S i).card)
        = ∑ i : Fin (n + 1), (discreteModifiedMetric HF (X i).val + 1) := by
    simp [hS_card]
  exact_mod_cast hmetric.trans (hcard.trans_eq hsum)

/-- Finite rooted overcount for the source-facing hard-core relation: summing
the modified-metric exponential weight over all polymers incompatible with a
fixed polymer `Q` is bounded by the number of active skeleton roots of `Q`
times the rooted geometric constant.

The proof uses only the exact incompatibility characterization of
`omegaHolePolymerSystem` and the previously verified rooted modified-metric
summability theorem. -/
theorem appendixFHole_incomp_expWeightSum_le_skeletonCard_mul
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (Q : OmegaPolymerType HF zK) (κ₀ : ℝ)
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne : ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1) :
    (∑ Q' ∈ (Finset.univ : Finset (OmegaPolymerType HF zK)).filter
        (fun Q' => (omegaHolePolymerSystem HF zK).incomp Q Q'),
      appendixFHoleExpWeight HF κ₀ Q'.val)
      ≤
    ((skeleton HF Q.val).card : ℝ) *
      appendixFHoleRootSumConstant d κ₀ := by
  classical
  let w : OmegaPolymerType HF zK → ℝ := fun Q' =>
    appendixFHoleExpWeight HF κ₀ Q'.val
  let incompFiber : Finset (OmegaPolymerType HF zK) :=
    (Finset.univ : Finset (OmegaPolymerType HF zK)).filter
      (fun Q' => (omegaHolePolymerSystem HF zK).incomp Q Q')
  let rootFiber : Cube d L → Finset (OmegaPolymerType HF zK) := fun r =>
    (Finset.univ : Finset (OmegaPolymerType HF zK)).filter
      (fun Q' => r ∈ skeleton HF Q'.val)
  have hw : ∀ Q' : OmegaPolymerType HF zK, 0 ≤ w Q' := by
    intro Q'
    exact appendixFHoleExpWeight_nonneg HF κ₀ Q'.val
  have hsub : incompFiber ⊆ (skeleton HF Q.val).biUnion rootFiber := by
    intro Q' hQ'
    dsimp [incompFiber] at hQ'
    rw [Finset.mem_filter] at hQ'
    have hinc : (omegaHolePolymerSystem HF zK).incomp Q Q' := hQ'.2
    rcases (omegaHolePolymerSystem_incomp_iff_exists HF zK Q Q').mp hinc
      with ⟨r, hrQ, hrQ'⟩
    rw [Finset.mem_biUnion]
    refine ⟨r, hrQ, ?_⟩
    dsimp [rootFiber]
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ Q', hrQ'⟩
  have hfinite :
      (∑ Q' ∈ incompFiber, w Q') ≤
        ∑ Q' ∈ (skeleton HF Q.val).biUnion rootFiber, w Q' := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun Q' _ _ => hw Q')
  have hbi :
      (∑ Q' ∈ (skeleton HF Q.val).biUnion rootFiber, w Q')
        ≤ ∑ r ∈ skeleton HF Q.val, ∑ Q' ∈ rootFiber r, w Q' := by
    exact sum_biUnion_le (skeleton HF Q.val)
      rootFiber w hw
  have hroot : ∀ r : Cube d L,
      (∑ Q' ∈ rootFiber r, w Q') ≤ appendixFHoleRootSumConstant d κ₀ := by
    intro r
    change
      (∑ Q' ∈ (Finset.univ : Finset (OmegaPolymerType HF zK)).filter
          (fun Q' => r ∈ skeleton HF Q'.val),
          appendixFHoleExpWeight HF κ₀ Q'.val)
        ≤ appendixFHoleRootSumConstant d κ₀
    simpa [appendixFHoleRootSumConstant] using
      appendixFHole_rootedFiniteExpWeightSum_le HF zK
        (Finset.univ : Finset (OmegaPolymerType HF zK)) r κ₀
        hdisj hnoedges hholes_ne hCq
  have hroots :
      (∑ r ∈ skeleton HF Q.val, ∑ Q' ∈ rootFiber r, w Q')
        ≤ ∑ _r ∈ skeleton HF Q.val,
          appendixFHoleRootSumConstant d κ₀ := by
    refine Finset.sum_le_sum ?_
    intro r _hr
    exact hroot r
  have hsum_const :
      (∑ _r ∈ skeleton HF Q.val,
        appendixFHoleRootSumConstant d κ₀)
        =
      ((skeleton HF Q.val).card : ℝ) *
        appendixFHoleRootSumConstant d κ₀ := by
    rw [sum_const, nsmul_eq_mul]
  change (∑ Q' ∈ incompFiber, w Q')
      ≤ ((skeleton HF Q.val).card : ℝ) *
        appendixFHoleRootSumConstant d κ₀
  exact hfinite.trans (hbi.trans (hroots.trans_eq hsum_const))

end YangMills.RG
