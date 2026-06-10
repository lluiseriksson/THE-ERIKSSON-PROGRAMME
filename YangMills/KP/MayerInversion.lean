/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.KP.Ursell
import YangMills.KP.Cluster

/-!
# Mayer–Ursell inversion, step 0 — the indicator identity

Opening bricks of B0a (`docs/CLUSTER-CORRELATION-PLAN.md` §2c): the
alternating sum over ALL spanning subgraphs of the incompatibility graph
is the compatibility indicator,

  `∑_{E ⊆ edges(G_X)} (−1)^{|E|} = 𝟙[X pairwise compatible]`,

via `Finset.sum_powerset_neg_one_pow_card`.  The forthcoming core of
B0a refines this by grouping `E` by its component partition, producing
`∑_π ∏_B ursell` on the left — the partition identity that drives
`Ξ = exp(clusterSum)`.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.KP

open scoped BigOperators

variable (P : PolymerSystem)

/-- A tuple is **pairwise compatible** when no two coordinates (equal or
not) carry incompatible polymers — the tuple-level admissibility that the
Mayer product detects.  (Repetitions die through `incomp_self`.) -/
def PairwiseCompatible {n : ℕ} (X : Fin n → P.Polymer) : Prop :=
  ∀ i j : Fin n, i ≠ j → ¬ P.incomp (X i) (X j)

open Classical in
/-- The incompatibility graph has no edges iff the tuple is pairwise
compatible. -/
lemma edgeFinset_eq_empty_iff {n : ℕ} (X : Fin n → P.Polymer) :
    (incompGraph P X).edgeFinset = ∅ ↔ PairwiseCompatible P X := by
  constructor
  · intro h i j hne hinc
    have hadj : (incompGraph P X).Adj i j :=
      (incompGraph_adj P X i j).mpr ⟨hne, hinc⟩
    have : s(i, j) ∈ (incompGraph P X).edgeFinset :=
      SimpleGraph.mem_edgeFinset.mpr hadj
    rw [h] at this
    exact absurd this (Finset.notMem_empty _)
  · intro h
    rw [Finset.eq_empty_iff_forall_notMem]
    intro e he
    induction e with
    | h i j =>
        have hadj := SimpleGraph.mem_edgeFinset.mp he
        have := (incompGraph_adj P X i j).mp hadj
        exact h i j this.1 this.2

open Classical in
/-- **The indicator identity (B0a, step 0):** the alternating sum over
all spanning subgraphs of the incompatibility graph is the pairwise-
compatibility indicator. -/
theorem sum_neg_one_pow_eq_indicator {n : ℕ} (X : Fin n → P.Polymer) :
    ∑ E ∈ (incompGraph P X).edgeFinset.powerset, (-1 : ℤ) ^ E.card
    = if PairwiseCompatible P X then 1 else 0 := by
  rw [Finset.sum_powerset_neg_one_pow_card]
  by_cases h : PairwiseCompatible P X
  · rw [if_pos ((edgeFinset_eq_empty_iff P X).mpr h), if_pos h]
  · rw [if_neg fun he => h ((edgeFinset_eq_empty_iff P X).mp he),
      if_neg h]

end YangMills.KP
