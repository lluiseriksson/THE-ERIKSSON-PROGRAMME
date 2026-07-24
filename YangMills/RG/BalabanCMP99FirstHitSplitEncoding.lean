/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99FirstHitSplitCount
import YangMills.RG.BalabanCMP99PatchedParametrixTerminalWalkCount

/-!
# Exact first-hit split encoding

A marked generated physical walk is encoded at its first marked domain by
the reversed prefix and the forward suffix.  Pointed path reversal is
involutive, while `take` and `drop` reconstruct the original tail.  Hence
the encoding is injective and the differentiated first-hit carrier really
counts the physical walks; it is not merely a formal overcount.
-/

namespace YangMills.RG

noncomputable section

universe u

/-- The terminal chart of the first `i` steps is the chart at index `i` in
the complete ordered domain path. -/
theorem terminalDomain_take_eq_domains_get
    {Domain : Type u}
    (head : Domain) (tail : List (CMP99WalkStep Unit Domain))
    (i : Fin
      ((⟨head, tail⟩ : CMP99GeneralizedWalk Unit Domain).domains.length)) :
    CMP99GeneralizedWalk.terminalDomain
        ⟨head, tail.take i.1⟩ =
      (⟨head, tail⟩ : CMP99GeneralizedWalk Unit Domain).domains.get i := by
  induction tail generalizing head with
  | nil =>
      rcases i with ⟨_ | k, hi⟩
      · simp [CMP99GeneralizedWalk.domains]
      · simp [CMP99GeneralizedWalk.domains] at hi
  | cons step rest ih =>
      cases i with
      | mk value hvalue =>
          cases value with
          | zero =>
              simp [CMP99GeneralizedWalk.domains]
          | succ k =>
              have hk :
                  k <
                    ((⟨step.domain, rest⟩ :
                      CMP99GeneralizedWalk Unit Domain).domains.length) := by
                simp [CMP99GeneralizedWalk.domains] at hvalue ⊢
                omega
              simpa [CMP99GeneralizedWalk.domains] using
                ih step.domain ⟨k, hk⟩

/-- Extensional membership in the nondependent first-hit carrier. -/
theorem mem_cmp99FirstHitSplitData_iff
    {Domain : Type u} [Fintype Domain] [DecidableEq Domain]
    (successors predecessors :
      Domain → Finset (CMP99WalkStep Unit Domain))
    (relevant : Finset Domain) (n : ℕ)
    (datum : CMP99FirstHitSplitDatum Domain) :
    datum ∈ cmp99FirstHitSplitData
        successors predecessors relevant n ↔
      ∃ i ∈ Finset.range (n + 1),
        ∃ pivotDomain ∈ relevant,
          ∃ preTail ∈ cmp99AdmissibleTails predecessors pivotDomain i,
            ∃ postTail ∈
                cmp99AdmissibleTails successors pivotDomain (n - i),
              (i, pivotDomain, preTail, postTail) = datum := by
  classical
  simp [cmp99FirstHitSplitData, cmp99FirstHitSplitDataAt]

/-- Encode a marked physical walk by its first marked chart, reversed
prefix, and forward suffix. -/
def cmp99PhysicalFirstHitSplitEncode
    {ι Cube : Type*} [DecidableEq ι] [DecidableEq Cube]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (R : ℕ)
    (domainActive : ↥charts → Finset Cube) (pivot : Cube) (n : ℕ)
    (walk : ↥(cmp99GeneratedWalksActivating
      (cmp99PhysicalPatchSuccessorSteps charts core enlarged dist R)
      domainActive pivot n)) :
    CMP99FirstHitSplitDatum ↥charts :=
  let idx := CMP99GeneratedWalkAtLength.firstActiveIndex walk
  let preTail := walk.1.2.1.take idx.1
  let pivotDomain := walk.1.toGeneralizedWalk.domains.get idx
  (idx.1, pivotDomain,
    cmp99ReversePhysicalPointedTail walk.1.1 preTail,
    walk.1.2.1.drop idx.1)

/-- The encoded prefix and suffix belong to the reverse and forward
generated families rooted at the first marked chart. -/
theorem cmp99PhysicalFirstHitSplitEncode_mapsTo
    {ι Cube : Type*} [DecidableEq ι] [DecidableEq Cube]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (R : ℕ)
    (domainActive : ↥charts → Finset Cube) (pivot : Cube) (n : ℕ) :
    Set.MapsTo
      (cmp99PhysicalFirstHitSplitEncode
        charts core enlarged dist R domainActive pivot n)
      (Finset.univ : Finset ↥(cmp99GeneratedWalksActivating
        (cmp99PhysicalPatchSuccessorSteps charts core enlarged dist R)
        domainActive pivot n))
      (cmp99FirstHitSplitData
        (cmp99PhysicalPatchSuccessorSteps charts core enlarged dist R)
        (cmp99PhysicalPatchPredecessorSteps charts core enlarged dist R)
        (Finset.univ.filter fun X => pivot ∈ domainActive X) n) := by
  classical
  intro walk _hwalk
  let idx := CMP99GeneratedWalkAtLength.firstActiveIndex walk
  let i := idx.1
  let tail := walk.1.2.1
  let preTail := tail.take i
  let pivotDomain := walk.1.toGeneralizedWalk.domains.get idx
  have hlen : tail.length = n :=
    length_eq_of_mem_cmp99AdmissibleTails
      (cmp99PhysicalPatchSuccessorSteps charts core enlarged dist R)
      walk.1.2.2
  have hi : i ≤ n := by
    have hidx := idx.2
    have hdomlen : walk.1.toGeneralizedWalk.domains.length = n + 1 := by
      rw [CMP99GeneralizedWalk.length_domains,
        CMP99GeneratedWalkAtLength.toGeneralizedWalk_length]
    change i < walk.1.toGeneralizedWalk.domains.length at hidx
    omega
  have hfull :
      (walk.1.1 :: tail.map CMP99WalkStep.domain).IsChain
        (fun a b : ↥charts =>
          CMP99PhysicalPatchCanFollow core enlarged dist R a b) :=
    chain_of_mem_cmp99PhysicalPatchAdmissibleTails
      charts core enlarged dist R walk.1.2.2
  have hpreTailChain :
      (walk.1.1 :: preTail.map CMP99WalkStep.domain).IsChain
        (fun a b : ↥charts =>
          CMP99PhysicalPatchCanFollow core enlarged dist R a b) := by
    simpa [preTail, List.map_take] using hfull.take (i + 1)
  have hpreTailLen : preTail.length = i := by
    simp [preTail, List.length_take, hlen, Nat.min_eq_left hi]
  have hpreTail :
      preTail ∈ cmp99AdmissibleTails
        (cmp99PhysicalPatchSuccessorSteps charts core enlarged dist R)
        walk.1.1 i := by
    exact (mem_cmp99AdmissibleTails_physicalPatch_iff
      charts core enlarged dist R).2 ⟨hpreTailLen, hpreTailChain⟩
  have hpivotTerminal :
      CMP99GeneralizedWalk.terminalDomain ⟨walk.1.1, preTail⟩ =
        pivotDomain := by
    exact terminalDomain_take_eq_domains_get walk.1.1 tail idx
  have hpre :
      cmp99ReversePhysicalPointedTail walk.1.1 preTail ∈
        cmp99AdmissibleTails
          (cmp99PhysicalPatchPredecessorSteps
            charts core enlarged dist R)
          pivotDomain i :=
    cmp99ReversePhysicalPointedTail_mem_reverseAdmissibleTails
      charts core enlarged dist R hpreTail hpivotTerminal
  have hdropPath :
      (walk.1.1 :: tail.map CMP99WalkStep.domain).drop i =
        pivotDomain :: (tail.drop i).map CMP99WalkStep.domain := by
    change walk.1.toGeneralizedWalk.domains.drop idx.1 =
      pivotDomain :: (tail.drop idx.1).map CMP99WalkStep.domain
    rw [List.drop_eq_getElem_cons idx.2]
    simp [pivotDomain, tail,
      CMP99GeneratedWalkAtLength.toGeneralizedWalk,
      CMP99GeneralizedWalk.domains, List.map_drop]
  have hsuffixChain :
      (pivotDomain :: (tail.drop i).map CMP99WalkStep.domain).IsChain
        (fun a b : ↥charts =>
          CMP99PhysicalPatchCanFollow core enlarged dist R a b) := by
    rw [← hdropPath]
    exact hfull.drop i
  have hsuffixLen : (tail.drop i).length = n - i := by
    simp [List.length_drop, hlen]
  have hpost :
      tail.drop i ∈ cmp99AdmissibleTails
        (cmp99PhysicalPatchSuccessorSteps charts core enlarged dist R)
        pivotDomain (n - i) := by
    exact (mem_cmp99AdmissibleTails_physicalPatch_iff
      charts core enlarged dist R).2 ⟨hsuffixLen, hsuffixChain⟩
  have hrelevant :
      pivotDomain ∈ Finset.univ.filter fun X => pivot ∈ domainActive X := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact CMP99GeneratedWalkAtLength.mem_domainActive_firstActiveIndex walk
  apply (mem_cmp99FirstHitSplitData_iff _ _ _ _ _).2
  refine ⟨i, Finset.mem_range.mpr (Nat.lt_succ_of_le hi),
    pivotDomain, hrelevant,
    cmp99ReversePhysicalPointedTail walk.1.1 preTail, hpre,
    tail.drop i, hpost, ?_⟩
  simp [cmp99PhysicalFirstHitSplitEncode, idx, i, tail, preTail,
    pivotDomain]

/-- The split encoding is injective.  Equality of the reversed prefixes
recovers both heads and prefixes by pointed-path involutivity; equality of
suffixes then reconstructs the complete tails. -/
theorem cmp99PhysicalFirstHitSplitEncode_injOn
    {ι Cube : Type*} [DecidableEq ι] [DecidableEq Cube]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (R : ℕ)
    (domainActive : ↥charts → Finset Cube) (pivot : Cube) (n : ℕ) :
    Set.InjOn
      (cmp99PhysicalFirstHitSplitEncode
        charts core enlarged dist R domainActive pivot n)
      (Finset.univ : Finset ↥(cmp99GeneratedWalksActivating
        (cmp99PhysicalPatchSuccessorSteps charts core enlarged dist R)
        domainActive pivot n)) := by
  intro left _hleft right _hright hEq
  let leftIdx := CMP99GeneratedWalkAtLength.firstActiveIndex left
  let rightIdx := CMP99GeneratedWalkAtLength.firstActiveIndex right
  let leftTail := left.1.2.1
  let rightTail := right.1.2.1
  let leftPre := leftTail.take leftIdx.1
  let rightPre := rightTail.take rightIdx.1
  let leftPivot := left.1.toGeneralizedWalk.domains.get leftIdx
  let rightPivot := right.1.toGeneralizedWalk.domains.get rightIdx
  have hi : leftIdx.1 = rightIdx.1 := by
    simpa [cmp99PhysicalFirstHitSplitEncode, leftIdx, rightIdx] using
      congrArg (fun datum : CMP99FirstHitSplitDatum ↥charts => datum.1) hEq
  have hpivot : leftPivot = rightPivot := by
    simpa [cmp99PhysicalFirstHitSplitEncode, leftIdx, rightIdx,
      leftPivot, rightPivot] using
      congrArg (fun datum : CMP99FirstHitSplitDatum ↥charts => datum.2.1) hEq
  have hrev :
      cmp99ReversePhysicalPointedTail left.1.1 leftPre =
        cmp99ReversePhysicalPointedTail right.1.1 rightPre := by
    simpa [cmp99PhysicalFirstHitSplitEncode, leftIdx, rightIdx,
      leftPre, rightPre, leftTail, rightTail] using
      congrArg
        (fun datum : CMP99FirstHitSplitDatum ↥charts => datum.2.2.1) hEq
  have hpost :
      leftTail.drop leftIdx.1 = rightTail.drop rightIdx.1 := by
    simpa [cmp99PhysicalFirstHitSplitEncode, leftIdx, rightIdx,
      leftTail, rightTail] using
      congrArg
        (fun datum : CMP99FirstHitSplitDatum ↥charts => datum.2.2.2) hEq
  have hterminalLeft :
      CMP99GeneralizedWalk.terminalDomain ⟨left.1.1, leftPre⟩ =
        leftPivot :=
    terminalDomain_take_eq_domains_get left.1.1 leftTail leftIdx
  have hterminalRight :
      CMP99GeneralizedWalk.terminalDomain ⟨right.1.1, rightPre⟩ =
        rightPivot :=
    terminalDomain_take_eq_domains_get right.1.1 rightTail rightIdx
  have hheadLeft :=
    terminalDomain_reversePhysicalPointedTail left.1.1 leftPre
  have hheadRight :=
    terminalDomain_reversePhysicalPointedTail right.1.1 rightPre
  rw [hterminalLeft, hpivot, hrev] at hheadLeft
  rw [hterminalRight] at hheadRight
  have hhead : left.1.1 = right.1.1 :=
    hheadLeft.symm.trans hheadRight
  have hpreLeft :=
    reversePhysicalPointedTail_involutive left.1.1 leftPre
  have hpreRight :=
    reversePhysicalPointedTail_involutive right.1.1 rightPre
  rw [hterminalLeft, hpivot, hrev] at hpreLeft
  rw [hterminalRight] at hpreRight
  have hpre : leftPre = rightPre :=
    hpreLeft.symm.trans hpreRight
  have htail : leftTail = rightTail := by
    calc
      leftTail =
          leftTail.take leftIdx.1 ++ leftTail.drop leftIdx.1 := by
            symm
            exact List.take_append_drop _ _
      _ = rightTail.take rightIdx.1 ++ rightTail.drop rightIdx.1 := by
            change leftPre ++ leftTail.drop leftIdx.1 =
              rightPre ++ rightTail.drop rightIdx.1
            rw [hpre, hpost]
      _ = rightTail := List.take_append_drop _ _
  apply Subtype.ext
  refine Sigma.ext hhead ?_
  have hset :
      cmp99AdmissibleTails
          (cmp99PhysicalPatchSuccessorSteps
            charts core enlarged dist R) left.1.1 n =
        cmp99AdmissibleTails
          (cmp99PhysicalPatchSuccessorSteps
            charts core enlarged dist R) right.1.1 n := by
    rw [hhead]
  have hpred :
      (fun tail : List (CMP99WalkStep Unit ↥charts) =>
        tail ∈ cmp99AdmissibleTails
          (cmp99PhysicalPatchSuccessorSteps
            charts core enlarged dist R) left.1.1 n) =
      (fun tail : List (CMP99WalkStep Unit ↥charts) =>
        tail ∈ cmp99AdmissibleTails
          (cmp99PhysicalPatchSuccessorSteps
            charts core enlarged dist R) right.1.1 n) := by
    rw [hset]
  apply (Subtype.heq_iff_coe_heq rfl (heq_of_eq hpred)).2
  exact heq_of_eq htail

/-- Marked physical generated walks inject into the counted first-hit split
carrier. -/
theorem card_cmp99GeneratedWalksActivating_le_firstHitSplitData
    {ι Cube : Type*} [DecidableEq ι] [DecidableEq Cube]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (R : ℕ)
    (domainActive : ↥charts → Finset Cube) (pivot : Cube) (n : ℕ) :
    (cmp99GeneratedWalksActivating
      (cmp99PhysicalPatchSuccessorSteps charts core enlarged dist R)
      domainActive pivot n).card ≤
      (cmp99FirstHitSplitData
        (cmp99PhysicalPatchSuccessorSteps charts core enlarged dist R)
        (cmp99PhysicalPatchPredecessorSteps charts core enlarged dist R)
        (Finset.univ.filter fun X => pivot ∈ domainActive X) n).card := by
  simpa using Finset.card_le_card_of_injOn
    (cmp99PhysicalFirstHitSplitEncode
      charts core enlarged dist R domainActive pivot n)
    (cmp99PhysicalFirstHitSplitEncode_mapsTo
      charts core enlarged dist R domainActive pivot n)
    (cmp99PhysicalFirstHitSplitEncode_injOn
      charts core enlarged dist R domainActive pivot n)

end

end YangMills.RG
