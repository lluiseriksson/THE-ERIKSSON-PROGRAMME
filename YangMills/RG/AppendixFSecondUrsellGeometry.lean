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

/-- A transparent envelope constant for rooted metric moments.  It dominates
`1`, the inverse spare decay `κ₀⁻¹`, and the rooted geometric constant. -/
noncomputable def appendixFSecondUrsellMomentConstant (d : ℕ) (κ₀ : ℝ) : ℝ :=
  max 1 (max κ₀⁻¹ (appendixFHoleRootSumConstant d κ₀))

theorem appendixFSecondUrsellMomentConstant_one_le
    (d : ℕ) (κ₀ : ℝ) :
    1 ≤ appendixFSecondUrsellMomentConstant d κ₀ := by
  exact le_max_left _ _

theorem appendixFSecondUrsellMomentConstant_inv_le
    (d : ℕ) (κ₀ : ℝ) :
    κ₀⁻¹ ≤ appendixFSecondUrsellMomentConstant d κ₀ := by
  exact (le_max_left _ _).trans (le_max_right _ _)

theorem appendixFSecondUrsellMomentConstant_root_le
    (d : ℕ) (κ₀ : ℝ) :
    appendixFHoleRootSumConstant d κ₀
      ≤ appendixFSecondUrsellMomentConstant d κ₀ := by
  exact (le_max_right _ _).trans (le_max_right _ _)

theorem appendixFSecondUrsellMomentConstant_nonneg
    (d : ℕ) (κ₀ : ℝ) :
    0 ≤ appendixFSecondUrsellMomentConstant d κ₀ :=
  (zero_le_one).trans (appendixFSecondUrsellMomentConstant_one_le d κ₀)

private theorem real_pow_div_factorial_le_exp {x : ℝ} (hx : 0 ≤ x)
    (j : ℕ) :
    x ^ j / (j.factorial : ℝ) ≤ Real.exp x := by
  have hnonneg :
      ∀ i ∈ Finset.range (j + 1), 0 ≤ x ^ i / (i.factorial : ℝ) := by
    intro i _hi
    exact div_nonneg (pow_nonneg hx i) (by positivity)
  have hsingle :
      x ^ j / (j.factorial : ℝ) ≤
        ∑ i ∈ Finset.range (j + 1), x ^ i / (i.factorial : ℝ) := by
    exact Finset.single_le_sum hnonneg (by simp)
  exact hsingle.trans (Real.sum_le_exp_of_nonneg hx (j + 1))

private theorem real_pow_le_factorial_mul_exp {x : ℝ} (hx : 0 ≤ x)
    (j : ℕ) :
    x ^ j ≤ (j.factorial : ℝ) * Real.exp x := by
  have h := real_pow_div_factorial_le_exp hx j
  have hfact : 0 < (j.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos j
  rw [div_le_iff₀ hfact] at h
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

private theorem metric_pow_exp_two_mul_le_factorial_inv_pow_exp
    {κ : ℝ} (hκ : 0 < κ) (j m : ℕ) :
    ((m : ℝ) ^ j) * Real.exp (-((2 * κ) * (m : ℝ))) ≤
      (j.factorial : ℝ) * κ⁻¹ ^ j *
        Real.exp (-(κ * (m : ℝ))) := by
  have hm_nonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hx : 0 ≤ κ * (m : ℝ) := mul_nonneg hκ.le hm_nonneg
  have hpow := real_pow_le_factorial_mul_exp hx j
  have hκpow_nonneg : 0 ≤ (κ ^ j)⁻¹ :=
    inv_nonneg.mpr (pow_nonneg hκ.le j)
  have hκpow_ne : κ ^ j ≠ 0 := pow_ne_zero j hκ.ne'
  have hmpow :
      (m : ℝ) ^ j ≤
        (κ ^ j)⁻¹ * ((j.factorial : ℝ) * Real.exp (κ * (m : ℝ))) := by
    calc
      (m : ℝ) ^ j = (κ ^ j)⁻¹ * ((κ * (m : ℝ)) ^ j) := by
        rw [mul_pow]
        rw [← mul_assoc]
        rw [inv_mul_cancel₀ hκpow_ne]
        simp
      _ ≤ (κ ^ j)⁻¹ *
            ((j.factorial : ℝ) * Real.exp (κ * (m : ℝ))) := by
          exact mul_le_mul_of_nonneg_left hpow hκpow_nonneg
  have hexp_nonneg : 0 ≤ Real.exp (-((2 * κ) * (m : ℝ))) :=
    Real.exp_nonneg _
  calc
    ((m : ℝ) ^ j) * Real.exp (-((2 * κ) * (m : ℝ)))
        ≤ ((κ ^ j)⁻¹ * ((j.factorial : ℝ) *
              Real.exp (κ * (m : ℝ)))) *
            Real.exp (-((2 * κ) * (m : ℝ))) :=
          mul_le_mul_of_nonneg_right hmpow hexp_nonneg
    _ = (j.factorial : ℝ) * (κ ^ j)⁻¹ *
          (Real.exp (κ * (m : ℝ)) *
            Real.exp (-((2 * κ) * (m : ℝ)))) := by ring
    _ = (j.factorial : ℝ) * (κ ^ j)⁻¹ *
          Real.exp (κ * (m : ℝ) + -((2 * κ) * (m : ℝ))) := by
          rw [Real.exp_add]
    _ = (j.factorial : ℝ) * κ⁻¹ ^ j *
          Real.exp (-(κ * (m : ℝ))) := by
          rw [inv_pow]
          ring_nf

private theorem metricMomentEnvelope_le
    {d : ℕ} {κ₀ : ℝ} (hκ₀ : 0 < κ₀) (j : ℕ) :
    (j.factorial : ℝ) * κ₀⁻¹ ^ j *
        appendixFHoleRootSumConstant d κ₀
      ≤
    (j.factorial : ℝ) *
      appendixFSecondUrsellMomentConstant d κ₀ ^ (j + 1) := by
  let C := appendixFSecondUrsellMomentConstant d κ₀
  have hC_nonneg : 0 ≤ C :=
    appendixFSecondUrsellMomentConstant_nonneg d κ₀
  have hC_inv : κ₀⁻¹ ≤ C :=
    appendixFSecondUrsellMomentConstant_inv_le d κ₀
  have hC_root : appendixFHoleRootSumConstant d κ₀ ≤ C :=
    appendixFSecondUrsellMomentConstant_root_le d κ₀
  have hinv_nonneg : 0 ≤ κ₀⁻¹ := inv_nonneg.mpr hκ₀.le
  have hinv_pow_nonneg : 0 ≤ κ₀⁻¹ ^ j := pow_nonneg hinv_nonneg j
  have hpow : κ₀⁻¹ ^ j ≤ C ^ j :=
    pow_le_pow_left₀ hinv_nonneg hC_inv j
  have hfactor :
      κ₀⁻¹ ^ j * appendixFHoleRootSumConstant d κ₀
        ≤ C ^ (j + 1) := by
    calc
      κ₀⁻¹ ^ j * appendixFHoleRootSumConstant d κ₀
          ≤ κ₀⁻¹ ^ j * C :=
            mul_le_mul_of_nonneg_left hC_root hinv_pow_nonneg
      _ ≤ C ^ j * C :=
            mul_le_mul_of_nonneg_right hpow hC_nonneg
      _ = C ^ (j + 1) := by
            rw [pow_succ]
  have hfact_nonneg : 0 ≤ (j.factorial : ℝ) := by positivity
  simpa [C, mul_assoc] using
    mul_le_mul_of_nonneg_left hfactor hfact_nonneg

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

/-- Target-preserving exponential extraction for the source-facing weighted
second-Ursell tree term.  If each vertex weight splits into a residual
modified-metric exponential times a new weight `u`, then the fixed-union tree
term can extract one exponential weight at the target `Y`.

The point is that this lemma is applied before marker insertion or global
vertex summation erase the exact union constraint `omegaClusterUnion X = Y`.
The proof uses the KP spanning tree to stitch the leaf modified metrics into
the target metric. -/
theorem appendixFHoleHsharpWeightedTreeTerm_le_targetExpWeight_mul
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w u : OmegaPolymerType HF zK → ℝ)
    (Y : Finset (Cube d L))
    (n : ℕ)
    (rate : ℝ)
    (hrate : 0 ≤ rate)
    (hw : ∀ P : OmegaPolymerType HF zK, 0 ≤ w P)
    (hu : ∀ P : OmegaPolymerType HF zK, 0 ≤ u P)
    (hsplit : ∀ P : OmegaPolymerType HF zK,
      w P ≤ appendixFHoleExpWeight HF rate P.val * u P) :
    appendixFHoleHsharpWeightedTreeTerm HF zK w Y n ≤
      appendixFHoleExpWeight HF rate Y *
        appendixFHoleHsharpWeightedTreeTerm HF zK u Y n := by
  classical
  let P := omegaHolePolymerSystem HF zK
  let target := appendixFHoleExpWeight HF rate Y
  let fiber : Finset (Fin (n + 1) → OmegaPolymerType HF zK) :=
    (Finset.univ :
        Finset (Fin (n + 1) → OmegaPolymerType HF zK)).filter
      (fun X => omegaClusterUnion HF zK X = Y)
  have hprod :
      ∀ (X : Fin (n + 1) → OmegaPolymerType HF zK),
        omegaClusterUnion HF zK X = Y →
        ∀ {T : Finset (Sym2 (Fin (n + 1)))},
          T ∈ KP.spanningTrees (KP.incompGraph P X) →
          ∏ i, w (X i) ≤ target * ∏ i, u (X i) := by
    intro X hX T hT
    let S : ℝ := ∑ i : Fin (n + 1),
      ((discreteModifiedMetric HF (X i).val + 1 : ℕ) : ℝ)
    let mY : ℝ := ((discreteModifiedMetric HF Y + 1 : ℕ) : ℝ)
    have hmetricUnion :
        ((discreteModifiedMetric HF (omegaClusterUnion HF zK X) + 1 : ℕ) : ℝ)
          ≤ S :=
      omegaClusterUnion_discreteModifiedMetric_add_one_le_sum_of_spanningTree
        HF zK X hT
    have hmetric : mY ≤ S := by
      simpa [mY, S, hX] using hmetricUnion
    have hexpProd :
        (∏ i : Fin (n + 1),
            appendixFHoleExpWeight HF rate (X i).val)
          ≤ target := by
      have hmul : rate * mY ≤ rate * S :=
        mul_le_mul_of_nonneg_left hmetric hrate
      have hexp :
          Real.exp (-(rate * S)) ≤ Real.exp (-(rate * mY)) :=
        Real.exp_le_exp.mpr (neg_le_neg hmul)
      have hprod_eq :
          (∏ i : Fin (n + 1),
              appendixFHoleExpWeight HF rate (X i).val)
            = Real.exp (-(rate * S)) := by
        calc
          (∏ i : Fin (n + 1),
              appendixFHoleExpWeight HF rate (X i).val)
              =
            Real.exp
              (∑ i : Fin (n + 1),
                -(rate *
                  (((discreteModifiedMetric HF (X i).val + 1 : ℕ) : ℝ)))) := by
                rw [Real.exp_sum]
                simp [appendixFHoleExpWeight]
          _ = Real.exp (-(rate * S)) := by
                have hsum :
                    (∑ i : Fin (n + 1),
                      -(rate *
                        (((discreteModifiedMetric HF (X i).val + 1 : ℕ) : ℝ))))
                      = -(rate * S) := by
                  calc
                    (∑ i : Fin (n + 1),
                      -(rate *
                        (((discreteModifiedMetric HF (X i).val + 1 : ℕ) : ℝ))))
                        =
                      -(∑ i : Fin (n + 1),
                        rate *
                          (((discreteModifiedMetric HF (X i).val + 1 : ℕ) : ℝ))) := by
                          rw [Finset.sum_neg_distrib]
                    _ = -(rate *
                          ∑ i : Fin (n + 1),
                            (((discreteModifiedMetric HF (X i).val + 1 : ℕ) : ℝ))) := by
                          rw [← Finset.mul_sum]
                    _ = -(rate * S) := by rfl
                rw [hsum]
      exact hprod_eq.trans_le (by simpa [target, mY, appendixFHoleExpWeight] using hexp)
    have hsplitProd :
        (∏ i : Fin (n + 1), w (X i)) ≤
          ∏ i : Fin (n + 1),
            appendixFHoleExpWeight HF rate (X i).val * u (X i) :=
      Finset.prod_le_prod
        (fun i _hi => hw (X i))
        (fun i _hi => hsplit (X i))
    have huProd : 0 ≤ ∏ i : Fin (n + 1), u (X i) :=
      Finset.prod_nonneg fun i _hi => hu (X i)
    calc
      (∏ i : Fin (n + 1), w (X i))
          ≤ ∏ i : Fin (n + 1),
              appendixFHoleExpWeight HF rate (X i).val * u (X i) :=
            hsplitProd
      _ =
          (∏ i : Fin (n + 1),
              appendixFHoleExpWeight HF rate (X i).val) *
            ∏ i : Fin (n + 1), u (X i) := by
            rw [Finset.prod_mul_distrib]
      _ ≤ target * ∏ i : Fin (n + 1), u (X i) :=
            mul_le_mul_of_nonneg_right hexpProd huProd
  have htrees :
      ∀ X ∈ fiber,
        (∑ _T ∈ KP.spanningTrees (KP.incompGraph P X),
            ∏ i, w (X i)) ≤
          target *
            ∑ _T ∈ KP.spanningTrees (KP.incompGraph P X),
              ∏ i, u (X i) := by
    intro X hXfiber
    have hX : omegaClusterUnion HF zK X = Y := by
      exact (Finset.mem_filter.mp hXfiber).2
    calc
      (∑ _T ∈ KP.spanningTrees (KP.incompGraph P X),
          ∏ i, w (X i))
          ≤ ∑ _T ∈ KP.spanningTrees (KP.incompGraph P X),
              target * ∏ i, u (X i) :=
            Finset.sum_le_sum fun T hT => hprod X hX hT
      _ =
          target *
            ∑ _T ∈ KP.spanningTrees (KP.incompGraph P X),
              ∏ i, u (X i) := by
            rw [Finset.mul_sum]
  have hfiber :
      (∑ X ∈ fiber,
          ∑ _T ∈ KP.spanningTrees (KP.incompGraph P X),
            ∏ i, w (X i)) ≤
        target *
          ∑ X ∈ fiber,
            ∑ _T ∈ KP.spanningTrees (KP.incompGraph P X),
              ∏ i, u (X i) := by
    calc
      (∑ X ∈ fiber,
          ∑ _T ∈ KP.spanningTrees (KP.incompGraph P X),
            ∏ i, w (X i))
          ≤ ∑ X ∈ fiber,
              target *
                ∑ _T ∈ KP.spanningTrees (KP.incompGraph P X),
                  ∏ i, u (X i) :=
            Finset.sum_le_sum fun X hX => htrees X hX
      _ =
          target *
            ∑ X ∈ fiber,
              ∑ _T ∈ KP.spanningTrees (KP.incompGraph P X),
                ∏ i, u (X i) := by
            rw [Finset.mul_sum]
  have hfinal :
      (((n + 1).factorial : ℝ))⁻¹ *
          (∑ X ∈ fiber,
            ∑ _T ∈ KP.spanningTrees (KP.incompGraph P X),
              ∏ i, w (X i)) ≤
        target *
          ((((n + 1).factorial : ℝ))⁻¹ *
            (∑ X ∈ fiber,
              ∑ _T ∈ KP.spanningTrees (KP.incompGraph P X),
                ∏ i, u (X i))) := by
    calc
      (((n + 1).factorial : ℝ))⁻¹ *
          (∑ X ∈ fiber,
            ∑ _T ∈ KP.spanningTrees (KP.incompGraph P X),
              ∏ i, w (X i))
          ≤ (((n + 1).factorial : ℝ))⁻¹ *
              (target *
                ∑ X ∈ fiber,
                  ∑ _T ∈ KP.spanningTrees (KP.incompGraph P X),
                    ∏ i, u (X i)) :=
            mul_le_mul_of_nonneg_left hfiber (by positivity)
      _ =
          target *
            ((((n + 1).factorial : ℝ))⁻¹ *
              (∑ X ∈ fiber,
                ∑ _T ∈ KP.spanningTrees (KP.incompGraph P X),
                  ∏ i, u (X i))) := by
            ring
  simpa [appendixFHoleHsharpWeightedTreeTerm, fiber, P, target] using hfinal

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

/-- Rooted finite metric-moment bound.  The extra factor
`(d_M(Q')+1)^j` is paid for by one spare exponential decay `κ₀`, using the
elementary inequality `x^j / j! ≤ exp x`, and the remaining `κ₀`-decay is
summed by the rooted modified-metric theorem. -/
theorem appendixFHole_rootedFiniteMetricMomentExpWeightSum_le
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF zK))
    (r : Cube d L) (κ₀ : ℝ) (j : ℕ)
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
    (∑ Q' ∈ Λ.filter (fun Q' => r ∈ skeleton HF Q'.val),
      (((discreteModifiedMetric HF Q'.val + 1 : ℕ) : ℝ) ^ j) *
        appendixFHoleExpWeight HF (2 * κ₀) Q'.val)
      ≤
    (j.factorial : ℝ) *
      appendixFSecondUrsellMomentConstant d κ₀ ^ (j + 1) := by
  classical
  let Cj : ℝ := (j.factorial : ℝ) * κ₀⁻¹ ^ j
  have hCj_nonneg : 0 ≤ Cj := by
    dsimp [Cj]
    positivity
  have hpoint :
      ∀ Q' ∈ Λ.filter (fun Q' => r ∈ skeleton HF Q'.val),
        (((discreteModifiedMetric HF Q'.val + 1 : ℕ) : ℝ) ^ j) *
          appendixFHoleExpWeight HF (2 * κ₀) Q'.val
          ≤
        Cj * appendixFHoleExpWeight HF κ₀ Q'.val := by
    intro Q' _hQ'
    simpa [Cj, appendixFHoleExpWeight, mul_assoc] using
      metric_pow_exp_two_mul_le_factorial_inv_pow_exp hκ₀ j
        (discreteModifiedMetric HF Q'.val + 1)
  have hsum_point :
      (∑ Q' ∈ Λ.filter (fun Q' => r ∈ skeleton HF Q'.val),
        (((discreteModifiedMetric HF Q'.val + 1 : ℕ) : ℝ) ^ j) *
          appendixFHoleExpWeight HF (2 * κ₀) Q'.val)
        ≤
      ∑ Q' ∈ Λ.filter (fun Q' => r ∈ skeleton HF Q'.val),
        Cj * appendixFHoleExpWeight HF κ₀ Q'.val := by
    refine Finset.sum_le_sum ?_
    intro Q' hQ'
    exact hpoint Q' hQ'
  have hfactor :
      (∑ Q' ∈ Λ.filter (fun Q' => r ∈ skeleton HF Q'.val),
        Cj * appendixFHoleExpWeight HF κ₀ Q'.val)
        =
      Cj *
        (∑ Q' ∈ Λ.filter (fun Q' => r ∈ skeleton HF Q'.val),
          appendixFHoleExpWeight HF κ₀ Q'.val) := by
    rw [Finset.mul_sum]
  have hroot :
      (∑ Q' ∈ Λ.filter (fun Q' => r ∈ skeleton HF Q'.val),
        appendixFHoleExpWeight HF κ₀ Q'.val)
        ≤ appendixFHoleRootSumConstant d κ₀ := by
    simpa [appendixFHoleRootSumConstant] using
      appendixFHole_rootedFiniteExpWeightSum_le HF zK Λ r κ₀
        hdisj hnoedges hholes_ne hCq
  calc
    (∑ Q' ∈ Λ.filter (fun Q' => r ∈ skeleton HF Q'.val),
      (((discreteModifiedMetric HF Q'.val + 1 : ℕ) : ℝ) ^ j) *
        appendixFHoleExpWeight HF (2 * κ₀) Q'.val)
        ≤
      ∑ Q' ∈ Λ.filter (fun Q' => r ∈ skeleton HF Q'.val),
        Cj * appendixFHoleExpWeight HF κ₀ Q'.val := hsum_point
    _ = Cj *
        (∑ Q' ∈ Λ.filter (fun Q' => r ∈ skeleton HF Q'.val),
          appendixFHoleExpWeight HF κ₀ Q'.val) := hfactor
    _ ≤ Cj * appendixFHoleRootSumConstant d κ₀ :=
        mul_le_mul_of_nonneg_left hroot hCj_nonneg
    _ ≤ (j.factorial : ℝ) *
        appendixFSecondUrsellMomentConstant d κ₀ ^ (j + 1) := by
        simpa [Cj, mul_assoc] using
          metricMomentEnvelope_le (d := d) hκ₀ j

/-- Target-contained finite metric-moment bound.  If a full target `Y` is
representable by an active connected with-holes cover, then all polymers in a
finite family whose full support is contained in `Y` can be summed by
overcounting through active skeleton roots in `Y`.  This is the root-sum
input needed by the later second-Ursell leaf-removal recursion. -/
theorem appendixFHole_containedMetricMomentExpWeightSum_le_metric_mul
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF zK))
    {Y : Finset (Cube d L)} (κ₀ : ℝ) (j : ℕ)
    (hκ₀ : 0 < κ₀)
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne : ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1)
    (hY : Y ∈ appendixFTargetRegion
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF zK => skeleton HF X.val)
      (fun X : OmegaPolymerType HF zK => X.val)
      Λ) :
    (∑ Q ∈ Λ.filter (fun Q => Q.val ⊆ Y),
      (((discreteModifiedMetric HF Q.val + 1 : ℕ) : ℝ) ^ j) *
        appendixFHoleExpWeight HF (2 * κ₀) Q.val)
      ≤
    (((discreteModifiedMetric HF Y + 1 : ℕ) : ℝ)) *
      ((j.factorial : ℝ) *
        appendixFSecondUrsellMomentConstant d κ₀ ^ (j + 1)) := by
  classical
  let w : OmegaPolymerType HF zK → ℝ := fun Q =>
    (((discreteModifiedMetric HF Q.val + 1 : ℕ) : ℝ) ^ j) *
      appendixFHoleExpWeight HF (2 * κ₀) Q.val
  let K₀ : ℝ :=
    (j.factorial : ℝ) *
      appendixFSecondUrsellMomentConstant d κ₀ ^ (j + 1)
  have hw : ∀ Q, Q ∈ Λ → 0 ≤ w Q := by
    intro Q _hQ
    dsimp [w]
    exact mul_nonneg (pow_nonneg (by positivity) j)
      (appendixFHoleExpWeight_nonneg HF (2 * κ₀) Q.val)
  have hK₀ : 0 ≤ K₀ := by
    dsimp [K₀]
    exact mul_nonneg (by positivity)
      (pow_nonneg (appendixFSecondUrsellMomentConstant_nonneg d κ₀) _)
  have hroot : ∀ r : Cube d L,
      (∑ Q ∈ Λ.filter
          (fun Q => r ∈ skeleton HF Q.val), w Q) ≤ K₀ := by
    intro r
    simpa [w, K₀] using
      appendixFHole_rootedFiniteMetricMomentExpWeightSum_le
        HF zK Λ r κ₀ j hκ₀ hdisj hnoedges hholes_ne hCq
  simpa [w, K₀] using
    appendixFHole_containedWeightSum_le_metric_mul_of_rooted
      HF zK Λ w hw hK₀ hroot hY

/-- Finite metric-moment bound over the source-facing hard-core
incompatibility fiber.  Incompatibility is overcounted through active skeleton
roots of `Q`; the number of such roots is then bounded by `d_M(Q)+1`. -/
theorem appendixFHole_incomp_expWeight_metricMomentSum_le_factorial_mul
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
    (∑ Q' ∈ (Finset.univ : Finset (OmegaPolymerType HF zK)).filter
        (fun Q' => (omegaHolePolymerSystem HF zK).incomp Q Q'),
      (((discreteModifiedMetric HF Q'.val + 1 : ℕ) : ℝ) ^ j) *
        appendixFHoleExpWeight HF (2 * κ₀) Q'.val)
      ≤
    (j.factorial : ℝ) *
      appendixFSecondUrsellMomentConstant d κ₀ ^ (j + 1) *
        (((discreteModifiedMetric HF Q.val + 1 : ℕ) : ℝ)) := by
  classical
  let w : OmegaPolymerType HF zK → ℝ := fun Q' =>
    (((discreteModifiedMetric HF Q'.val + 1 : ℕ) : ℝ) ^ j) *
      appendixFHoleExpWeight HF (2 * κ₀) Q'.val
  let incompFiber : Finset (OmegaPolymerType HF zK) :=
    (Finset.univ : Finset (OmegaPolymerType HF zK)).filter
      (fun Q' => (omegaHolePolymerSystem HF zK).incomp Q Q')
  let rootFiber : Cube d L → Finset (OmegaPolymerType HF zK) := fun r =>
    (Finset.univ : Finset (OmegaPolymerType HF zK)).filter
      (fun Q' => r ∈ skeleton HF Q'.val)
  have hw : ∀ Q' : OmegaPolymerType HF zK, 0 ≤ w Q' := by
    intro Q'
    dsimp [w]
    exact mul_nonneg (pow_nonneg (by positivity) j)
      (appendixFHoleExpWeight_nonneg HF (2 * κ₀) Q'.val)
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
    exact sum_biUnion_le (skeleton HF Q.val) rootFiber w hw
  have hroot : ∀ r : Cube d L,
      (∑ Q' ∈ rootFiber r, w Q')
        ≤ (j.factorial : ℝ) *
          appendixFSecondUrsellMomentConstant d κ₀ ^ (j + 1) := by
    intro r
    change
      (∑ Q' ∈ (Finset.univ : Finset (OmegaPolymerType HF zK)).filter
          (fun Q' => r ∈ skeleton HF Q'.val),
        (((discreteModifiedMetric HF Q'.val + 1 : ℕ) : ℝ) ^ j) *
          appendixFHoleExpWeight HF (2 * κ₀) Q'.val)
        ≤ (j.factorial : ℝ) *
          appendixFSecondUrsellMomentConstant d κ₀ ^ (j + 1)
    exact appendixFHole_rootedFiniteMetricMomentExpWeightSum_le
      HF zK (Finset.univ : Finset (OmegaPolymerType HF zK)) r κ₀ j
      hκ₀ hdisj hnoedges hholes_ne hCq
  have hroots :
      (∑ r ∈ skeleton HF Q.val, ∑ Q' ∈ rootFiber r, w Q')
        ≤ ∑ _r ∈ skeleton HF Q.val,
          (j.factorial : ℝ) *
            appendixFSecondUrsellMomentConstant d κ₀ ^ (j + 1) := by
    refine Finset.sum_le_sum ?_
    intro r _hr
    exact hroot r
  have hsum_const :
      (∑ _r ∈ skeleton HF Q.val,
        (j.factorial : ℝ) *
          appendixFSecondUrsellMomentConstant d κ₀ ^ (j + 1))
        =
      ((skeleton HF Q.val).card : ℝ) *
        ((j.factorial : ℝ) *
          appendixFSecondUrsellMomentConstant d κ₀ ^ (j + 1)) := by
    rw [sum_const, nsmul_eq_mul]
  have hcard :
      ((skeleton HF Q.val).card : ℝ) ≤
        (((discreteModifiedMetric HF Q.val + 1 : ℕ) : ℝ)) := by
    exact_mod_cast
      skeleton_card_le_discreteModifiedMetric_add_one HF Q.val
        Q.property.right.left
  have hconst_nonneg :
      0 ≤ (j.factorial : ℝ) *
        appendixFSecondUrsellMomentConstant d κ₀ ^ (j + 1) := by
    exact mul_nonneg (by positivity)
      (pow_nonneg (appendixFSecondUrsellMomentConstant_nonneg d κ₀) _)
  change (∑ Q' ∈ incompFiber, w Q')
      ≤ (j.factorial : ℝ) *
        appendixFSecondUrsellMomentConstant d κ₀ ^ (j + 1) *
          (((discreteModifiedMetric HF Q.val + 1 : ℕ) : ℝ))
  calc
    (∑ Q' ∈ incompFiber, w Q')
        ≤ ∑ Q' ∈ (skeleton HF Q.val).biUnion rootFiber, w Q' := hfinite
    _ ≤ ∑ r ∈ skeleton HF Q.val, ∑ Q' ∈ rootFiber r, w Q' := hbi
    _ ≤ ∑ _r ∈ skeleton HF Q.val,
          (j.factorial : ℝ) *
            appendixFSecondUrsellMomentConstant d κ₀ ^ (j + 1) := hroots
    _ = ((skeleton HF Q.val).card : ℝ) *
        ((j.factorial : ℝ) *
          appendixFSecondUrsellMomentConstant d κ₀ ^ (j + 1)) := hsum_const
    _ ≤ (((discreteModifiedMetric HF Q.val + 1 : ℕ) : ℝ)) *
        ((j.factorial : ℝ) *
          appendixFSecondUrsellMomentConstant d κ₀ ^ (j + 1)) :=
          mul_le_mul_of_nonneg_right hcard hconst_nonneg
    _ = (j.factorial : ℝ) *
        appendixFSecondUrsellMomentConstant d κ₀ ^ (j + 1) *
          (((discreteModifiedMetric HF Q.val + 1 : ℕ) : ℝ)) := by ring

end YangMills.RG
