/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99PivotedGeneratedWalk

/-!
# Cardinality of first-hit split data

A marked length-`n` physical walk can be encoded by its first marked
occurrence, a reverse-generated prefix, and a forward-generated suffix.  This
file counts that target data before constructing the source encoding.
-/

namespace YangMills.RG

noncomputable section

universe u

/-- Nondependent carrier for one first-hit split. -/
abbrev CMP99FirstHitSplitDatum (Domain : Type u) :=
  ℕ × Domain ×
    List (CMP99WalkStep Unit Domain) ×
      List (CMP99WalkStep Unit Domain)

/-- Split data with a prescribed first-hit position. -/
noncomputable def cmp99FirstHitSplitDataAt
    {Domain : Type u} [Fintype Domain] [DecidableEq Domain]
    (successors predecessors :
      Domain → Finset (CMP99WalkStep Unit Domain))
    (relevant : Finset Domain) (n i : ℕ) :
    Finset (CMP99FirstHitSplitDatum Domain) :=
  relevant.biUnion fun pivotDomain =>
    (cmp99AdmissibleTails predecessors pivotDomain i).biUnion fun preTail =>
      (cmp99AdmissibleTails successors pivotDomain (n - i)).image fun postTail =>
        (i, pivotDomain, preTail, postTail)

/-- All legal split positions `0,...,n`. -/
noncomputable def cmp99FirstHitSplitData
    {Domain : Type u} [Fintype Domain] [DecidableEq Domain]
    (successors predecessors :
      Domain → Finset (CMP99WalkStep Unit Domain))
    (relevant : Finset Domain) (n : ℕ) :
    Finset (CMP99FirstHitSplitDatum Domain) :=
  (Finset.range (n + 1)).biUnion fun i =>
    cmp99FirstHitSplitDataAt successors predecessors relevant n i

/-- One position contributes at most the marked-domain count times the
reverse and forward branching powers. -/
theorem card_cmp99FirstHitSplitDataAt_le
    {Domain : Type u} [Fintype Domain] [DecidableEq Domain]
    (successors predecessors :
      Domain → Finset (CMP99WalkStep Unit Domain))
    (relevant : Finset Domain) (K n i : ℕ)
    (hforward : ∀ X k,
      (cmp99AdmissibleTails successors X k).card ≤ K ^ k)
    (hreverse : ∀ X k,
      (cmp99AdmissibleTails predecessors X k).card ≤ K ^ k) :
    (cmp99FirstHitSplitDataAt
      successors predecessors relevant n i).card ≤
      relevant.card * (K ^ i * K ^ (n - i)) := by
  classical
  calc
    (cmp99FirstHitSplitDataAt
        successors predecessors relevant n i).card ≤
        ∑ X ∈ relevant,
          ((cmp99AdmissibleTails predecessors X i).biUnion fun preTail =>
            (cmp99AdmissibleTails successors X (n - i)).image fun postTail =>
              (i, X, preTail, postTail)).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _X ∈ relevant, K ^ i * K ^ (n - i) := by
      gcongr with X hX
      calc
        ((cmp99AdmissibleTails predecessors X i).biUnion fun preTail =>
            (cmp99AdmissibleTails successors X (n - i)).image fun postTail =>
              (i, X, preTail, postTail)).card ≤
            ∑ preTail ∈ cmp99AdmissibleTails predecessors X i,
              ((cmp99AdmissibleTails successors X (n - i)).image
                fun postTail => (i, X, preTail, postTail)).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _preTail ∈ cmp99AdmissibleTails predecessors X i,
              K ^ (n - i) := by
          gcongr with preTail hpreTail
          exact (Finset.card_image_le).trans (hforward X (n - i))
        _ = (cmp99AdmissibleTails predecessors X i).card *
              K ^ (n - i) := by simp
        _ ≤ K ^ i * K ^ (n - i) :=
          Nat.mul_le_mul_right (K ^ (n - i)) (hreverse X i)
    _ = relevant.card * (K ^ i * K ^ (n - i)) := by simp

/-- The complete first-hit split carrier has the differentiated geometric
count `(n+1) * |relevant| * K^n`. -/
theorem card_cmp99FirstHitSplitData_le
    {Domain : Type u} [Fintype Domain] [DecidableEq Domain]
    (successors predecessors :
      Domain → Finset (CMP99WalkStep Unit Domain))
    (relevant : Finset Domain) (K n : ℕ)
    (hforward : ∀ X k,
      (cmp99AdmissibleTails successors X k).card ≤ K ^ k)
    (hreverse : ∀ X k,
      (cmp99AdmissibleTails predecessors X k).card ≤ K ^ k) :
    (cmp99FirstHitSplitData
      successors predecessors relevant n).card ≤
      (n + 1) * relevant.card * K ^ n := by
  classical
  calc
    (cmp99FirstHitSplitData
        successors predecessors relevant n).card ≤
        ∑ i ∈ Finset.range (n + 1),
          (cmp99FirstHitSplitDataAt
            successors predecessors relevant n i).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ Finset.range (n + 1),
          relevant.card * K ^ n := by
      gcongr with i hi
      have hin : i ≤ n := by
        simpa [Finset.mem_range] using Nat.le_of_lt_succ
          (Finset.mem_range.mp hi)
      calc
        (cmp99FirstHitSplitDataAt
            successors predecessors relevant n i).card ≤
            relevant.card * (K ^ i * K ^ (n - i)) :=
          card_cmp99FirstHitSplitDataAt_le
            successors predecessors relevant K n i hforward hreverse
        _ = relevant.card * K ^ n := by
          rw [← pow_add, Nat.add_comm i (n - i),
            Nat.sub_add_cancel hin]
    _ = (n + 1) * relevant.card * K ^ n := by
      simp
      ring

end

end YangMills.RG
