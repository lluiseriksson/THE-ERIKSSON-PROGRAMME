/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99PatchedParametrixSparseWalkBranching

/-!
# Head-anchored sparse CMP99 patched walks

The original sparse-word filter removes forbidden transitions between
continuation factors.  A source walk also has a distinguished head.  This
file proves that a head followed by a range-separated first continuation is
exactly zero, and hence refines every sparse layer to words whose first step
is physically admissible from that head.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- A separated first continuation is annihilated by the core projection in
the distinguished head. -/
theorem cmp99PhysicalPatchHead_mul_continuation_eq_zero_of_rangeSeparated
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι)
    (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    (hsub : ∀ i, i ∈ charts → core i ⊆ enlarged i)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) {R : ℕ}
    (hrange : PhysicalCovarianceFiniteRange K dist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (left right : ↥charts)
    (hsep : CMP99PhysicalRangeSeparated dist R (core left) (enlarged right)) :
    cmp99PhysicalPatchHead charts K enlarged core hc hmass hK left *
      cmp99PhysicalPatchContinuation
        charts K enlarged core hc hmass hK right = 0 := by
  let Cleft : PhysicalEndomorphism d N Nc :=
    cmp99LocalizedPhysicalCovariance K (enlarged left) hc hmass hK
  let Dright : PhysicalEndomorphism d N Nc :=
    (K - cmp99LocalizedPhysicalPrecision K (enlarged right) mass).comp
      ((cmp99LocalizedPhysicalCovariance K (enlarged right) hc hmass hK).comp
        (physicalBondProjection (core right)))
  have hproj :
      (physicalBondProjection (core left) : PhysicalEndomorphism d N Nc).comp
          Dright = 0 :=
    physicalBondProjection_comp_singleDefect_eq_zero_of_rangeSeparated
      K (core left) (core right) (enlarged right)
      (hsub right right.property) dist hrange hsep hc hmass hK
  apply ContinuousLinearMap.ext
  intro x
  change Cleft (physicalBondProjection (core left) (-Dright x)) = 0
  have hx := DFunLike.congr_fun hproj x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] at hx
  rw [map_neg, hx, neg_zero, map_zero]

/-- Physically admissible continuation tuples including the transition from
the distinguished head to the first continuation. -/
noncomputable def cmp99PhysicalPatchHeadAnchoredAdmissibleWords
    {ι : Type*} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (R : ℕ)
    (left : ↥charts) (n : ℕ) :
    Finset (Fin n → ↥charts) := by
  classical
  exact Finset.univ.filter fun word =>
    (left :: List.ofFn word).IsChain
      (fun a b : ↥charts =>
        CMP99PhysicalPatchCanFollow core enlarged dist R a b)

/-- Forgetting the head transition gives the earlier continuation-only sparse
word condition. -/
theorem cmp99PhysicalPatchHeadAnchoredAdmissibleWords_subset
    {ι : Type*} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (R : ℕ)
    (left : ↥charts) (n : ℕ) :
    cmp99PhysicalPatchHeadAnchoredAdmissibleWords
        charts core enlarged dist R left n ⊆
      cmp99PhysicalPatchAdmissibleWords
        charts core enlarged dist R n := by
  classical
  intro word hword
  rw [cmp99PhysicalPatchHeadAnchoredAdmissibleWords,
    Finset.mem_filter] at hword
  rw [cmp99PhysicalPatchAdmissibleWords, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, by
    simpa using hword.2.tail⟩

/-- If a continuation-only admissible word is not anchored at its head, its
complete ordered term is exactly zero. -/
theorem cmp99SingleSpeciesWalk_term_eq_zero_of_not_headAnchored
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι)
    (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    (hsub : ∀ i, i ∈ charts → core i ⊆ enlarged i)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) {R : ℕ}
    (hrange : PhysicalCovarianceFiniteRange K dist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (left : ↥charts) {n : ℕ} (word : Fin n → ↥charts)
    (hword : word ∈ cmp99PhysicalPatchAdmissibleWords
      charts core enlarged dist R n)
    (hnot : word ∉ cmp99PhysicalPatchHeadAnchoredAdmissibleWords
      charts core enlarged dist R left n) :
    (cmp99SingleSpeciesWalk left word).term
        (cmp99PhysicalPatchHead charts K enlarged core hc hmass hK)
        (fun _ => cmp99PhysicalPatchContinuation
          charts K enlarged core hc hmass hK) = 0 := by
  classical
  cases n with
  | zero =>
      exfalso
      apply hnot
      rw [cmp99PhysicalPatchHeadAnchoredAdmissibleWords,
        Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by simp⟩
  | succ n =>
      have htail :
          (List.ofFn word).IsChain
            (fun a b : ↥charts =>
              CMP99PhysicalPatchCanFollow core enlarged dist R a b) := by
        simpa [cmp99PhysicalPatchAdmissibleWords] using hword
      have hnotNear :
          ¬CMP99PhysicalPatchCanFollow core enlarged dist R left (word 0) := by
        intro hnear
        apply hnot
        rw [cmp99PhysicalPatchHeadAnchoredAdmissibleWords,
          Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [List.ofFn_succ] at htail ⊢
        exact List.IsChain.cons_cons hnear htail
      have hsep :
          CMP99PhysicalRangeSeparated dist R
            (core left) (enlarged (word 0)) := by
        simpa [CMP99PhysicalPatchCanFollow] using hnotNear
      have hzero :=
        cmp99PhysicalPatchHead_mul_continuation_eq_zero_of_rangeSeparated
          charts K enlarged core hsub dist hrange hc hmass hK
          left (word 0) hsep
      rw [cmp99SingleSpeciesWalk_term, cmp99OrderedTupleProduct,
        List.ofFn_succ, List.map_cons, List.prod_cons, ← mul_assoc,
        hzero, zero_mul]

/-- The continuation-only sparse sum equals the genuinely head-anchored
sparse sum.  Thus the exact layer can be indexed by physical anchored walks
without changing its value. -/
theorem sum_cmp99PhysicalPatchAdmissibleWords_eq_headAnchored
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι)
    (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    (hsub : ∀ i, i ∈ charts → core i ⊆ enlarged i)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) {R : ℕ}
    (hrange : PhysicalCovarianceFiniteRange K dist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (left : ↥charts) (n : ℕ) :
    (∑ word ∈ cmp99PhysicalPatchAdmissibleWords
        charts core enlarged dist R n,
      (cmp99SingleSpeciesWalk left word).term
        (cmp99PhysicalPatchHead charts K enlarged core hc hmass hK)
        (fun _ => cmp99PhysicalPatchContinuation
          charts K enlarged core hc hmass hK)) =
      ∑ word ∈ cmp99PhysicalPatchHeadAnchoredAdmissibleWords
          charts core enlarged dist R left n,
        (cmp99SingleSpeciesWalk left word).term
          (cmp99PhysicalPatchHead charts K enlarged core hc hmass hK)
          (fun _ => cmp99PhysicalPatchContinuation
            charts K enlarged core hc hmass hK) := by
  classical
  symm
  apply Finset.sum_subset
    (cmp99PhysicalPatchHeadAnchoredAdmissibleWords_subset
      charts core enlarged dist R left n)
  intro word hword hnot
  exact cmp99SingleSpeciesWalk_term_eq_zero_of_not_headAnchored
    charts K enlarged core hsub dist hrange hc hmass hK
    left word hword hnot

/-- Physical generated tails are characterized exactly by their length and
the head-anchored near-range chain.  This is the converse of the previously
available soundness lemmas. -/
theorem mem_cmp99AdmissibleTails_physicalPatch_iff
    {ι : Type*} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (R : ℕ) :
    ∀ {n : ℕ} {left : ↥charts}
      {tail : List (CMP99WalkStep Unit ↥charts)},
      tail ∈ cmp99AdmissibleTails
          (cmp99PhysicalPatchSuccessorSteps
            charts core enlarged dist R) left n ↔
        tail.length = n ∧
          (left :: tail.map CMP99WalkStep.domain).IsChain
            (fun a b : ↥charts =>
              CMP99PhysicalPatchCanFollow core enlarged dist R a b) := by
  intro n
  induction n with
  | zero =>
      intro left tail
      constructor
      · intro htail
        have hnil : tail = [] := by
          simpa [cmp99AdmissibleTails] using htail
        subst hnil
        simp
      · rintro ⟨hlen, _hchain⟩
        have hnil : tail = [] := List.eq_nil_of_length_eq_zero hlen
        subst hnil
        simp [cmp99AdmissibleTails]
  | succ n ih =>
      intro left tail
      constructor
      · intro htail
        exact ⟨
          length_eq_of_mem_cmp99AdmissibleTails
            (cmp99PhysicalPatchSuccessorSteps
              charts core enlarged dist R) htail,
          chain_of_mem_cmp99PhysicalPatchAdmissibleTails
            charts core enlarged dist R htail⟩
      · rintro ⟨hlen, hchain⟩
        cases tail with
        | nil => simp at hlen
        | cons step rest =>
            rw [cmp99AdmissibleTails, Finset.mem_biUnion]
            refine ⟨step, ?_, ?_⟩
            · rw [mem_cmp99PhysicalPatchSuccessorSteps_iff]
              exact hchain.rel_head
            · rw [Finset.mem_image]
              refine ⟨rest, ?_, rfl⟩
              apply (ih (left := step.domain) (tail := rest)).2
              constructor
              · simpa using hlen
              · simpa using hchain.tail

/-- Convert a `Fin n` continuation word to the unique-label source-step list
used by `CMP99AnchoredWalk`. -/
def cmp99PhysicalPatchStepsOfWord
    {ι : Type*} {charts : Finset ι} {n : ℕ}
    (word : Fin n → ↥charts) :
    List (CMP99WalkStep Unit ↥charts) :=
  (List.ofFn word).map fun domain => ⟨(), domain⟩

@[simp]
theorem length_cmp99PhysicalPatchStepsOfWord
    {ι : Type*} {charts : Finset ι} {n : ℕ}
    (word : Fin n → ↥charts) :
    (cmp99PhysicalPatchStepsOfWord word).length = n := by
  simp [cmp99PhysicalPatchStepsOfWord]

@[simp]
theorem map_domain_cmp99PhysicalPatchStepsOfWord
    {ι : Type*} {charts : Finset ι} {n : ℕ}
    (word : Fin n → ↥charts) :
    (cmp99PhysicalPatchStepsOfWord word).map CMP99WalkStep.domain =
      List.ofFn word := by
  rw [cmp99PhysicalPatchStepsOfWord, List.map_map]
  change List.map id (List.ofFn word) = List.ofFn word
  simp

/-- A head-anchored admissible tuple produces a certified generated tail. -/
theorem cmp99PhysicalPatchStepsOfWord_mem_admissibleTails
    {ι : Type*} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (R : ℕ)
    (left : ↥charts) {n : ℕ} (word : Fin n → ↥charts)
    (hword : word ∈ cmp99PhysicalPatchHeadAnchoredAdmissibleWords
      charts core enlarged dist R left n) :
    cmp99PhysicalPatchStepsOfWord word ∈
      cmp99AdmissibleTails
        (cmp99PhysicalPatchSuccessorSteps charts core enlarged dist R)
        left n := by
  classical
  apply (mem_cmp99AdmissibleTails_physicalPatch_iff
    charts core enlarged dist R).2
  constructor
  · exact length_cmp99PhysicalPatchStepsOfWord word
  · rw [map_domain_cmp99PhysicalPatchStepsOfWord]
    simpa [cmp99PhysicalPatchHeadAnchoredAdmissibleWords] using hword

/-- Forget a certified generated tail and read its ordered domains as a
`Fin n` tuple. -/
noncomputable def cmp99PhysicalPatchWordOfTail
    {ι : Type*} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (R : ℕ)
    (left : ↥charts) {n : ℕ}
    (tail : ↥(cmp99AdmissibleTails
      (cmp99PhysicalPatchSuccessorSteps charts core enlarged dist R)
      left n)) :
    Fin n → ↥charts :=
  fun i =>
    (tail.1.get ⟨i.1, by
      have hlen := length_eq_of_mem_cmp99AdmissibleTails
        (cmp99PhysicalPatchSuccessorSteps charts core enlarged dist R)
        tail.2
      omega⟩).domain

/-- Reading the domains of a generated tail and rebuilding its list recovers
the original domain list. -/
theorem ofFn_cmp99PhysicalPatchWordOfTail
    {ι : Type*} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (R : ℕ)
    (left : ↥charts) {n : ℕ}
    (tail : ↥(cmp99AdmissibleTails
      (cmp99PhysicalPatchSuccessorSteps charts core enlarged dist R)
      left n)) :
    List.ofFn (cmp99PhysicalPatchWordOfTail
      charts core enlarged dist R left tail) =
      tail.1.map CMP99WalkStep.domain := by
  classical
  apply List.ext_get
  · have hlen := length_eq_of_mem_cmp99AdmissibleTails
      (cmp99PhysicalPatchSuccessorSteps charts core enlarged dist R) tail.2
    simp [hlen]
  · intro i hi₁ hi₂
    simp [cmp99PhysicalPatchWordOfTail]

/-- The tuple read from a certified tail is head-anchored admissible. -/
theorem cmp99PhysicalPatchWordOfTail_mem_headAnchored
    {ι : Type*} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (R : ℕ)
    (left : ↥charts) {n : ℕ}
    (tail : ↥(cmp99AdmissibleTails
      (cmp99PhysicalPatchSuccessorSteps charts core enlarged dist R)
      left n)) :
    cmp99PhysicalPatchWordOfTail charts core enlarged dist R left tail ∈
      cmp99PhysicalPatchHeadAnchoredAdmissibleWords
        charts core enlarged dist R left n := by
  classical
  rw [cmp99PhysicalPatchHeadAnchoredAdmissibleWords,
    Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [ofFn_cmp99PhysicalPatchWordOfTail]
  exact chain_of_mem_cmp99PhysicalPatchAdmissibleTails
    charts core enlarged dist R tail.2

/-- Exact equivalence between the head-anchored `Fin n` words and the
generated length-`n` tails used by `CMP99AnchoredWalk`. -/
noncomputable def cmp99PhysicalPatchHeadAnchoredWordsEquivTails
    {ι : Type*} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (R : ℕ)
    (left : ↥charts) (n : ℕ) :
    ↥(cmp99PhysicalPatchHeadAnchoredAdmissibleWords
      charts core enlarged dist R left n) ≃
      ↥(cmp99AdmissibleTails
        (cmp99PhysicalPatchSuccessorSteps charts core enlarged dist R)
        left n) where
  toFun word := ⟨cmp99PhysicalPatchStepsOfWord word.1,
    cmp99PhysicalPatchStepsOfWord_mem_admissibleTails
      charts core enlarged dist R left word.1 word.2⟩
  invFun tail := ⟨
    cmp99PhysicalPatchWordOfTail charts core enlarged dist R left tail,
    cmp99PhysicalPatchWordOfTail_mem_headAnchored
      charts core enlarged dist R left tail⟩
  left_inv word := by
    apply Subtype.ext
    funext i
    simp [cmp99PhysicalPatchWordOfTail,
      cmp99PhysicalPatchStepsOfWord]
  right_inv tail := by
    apply Subtype.ext
    have hdomains := ofFn_cmp99PhysicalPatchWordOfTail
      charts core enlarged dist R left tail
    change cmp99PhysicalPatchStepsOfWord
      (cmp99PhysicalPatchWordOfTail
        charts core enlarged dist R left tail) = tail.1
    rw [cmp99PhysicalPatchStepsOfWord, hdomains, List.map_map]
    induction tail.1 with
    | nil => rfl
    | cons step rest ih =>
        cases step with
        | mk label domain =>
            cases label
            simp only [List.map_cons, Function.comp_apply]
            rw [ih]

/-- Finite operator sums are preserved by the exact equivalence between
head-anchored words and generated tails. -/
theorem sum_cmp99PhysicalPatchHeadAnchoredWords_eq_admissibleTails
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι)
    (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (R : ℕ)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (left : ↥charts) (n : ℕ) :
    (∑ word ∈ cmp99PhysicalPatchHeadAnchoredAdmissibleWords
        charts core enlarged dist R left n,
      (cmp99SingleSpeciesWalk left word).term
        (cmp99PhysicalPatchHead charts K enlarged core hc hmass hK)
        (fun _ => cmp99PhysicalPatchContinuation
          charts K enlarged core hc hmass hK)) =
      ∑ tail : ↥(cmp99AdmissibleTails
          (cmp99PhysicalPatchSuccessorSteps
            charts core enlarged dist R) left n),
        (CMP99AnchoredWalk.toGeneralizedWalk
          (⟨n, tail⟩ : CMP99AnchoredWalk
            (cmp99PhysicalPatchSuccessorSteps
              charts core enlarged dist R) left)).term
          (cmp99PhysicalPatchHead charts K enlarged core hc hmass hK)
          (fun _ => cmp99PhysicalPatchContinuation
            charts K enlarged core hc hmass hK) := by
  classical
  rw [← Finset.sum_coe_sort]
  let e := cmp99PhysicalPatchHeadAnchoredWordsEquivTails
    charts core enlarged dist R left n
  let f :
      ↥(cmp99AdmissibleTails
        (cmp99PhysicalPatchSuccessorSteps charts core enlarged dist R)
        left n) → PhysicalEndomorphism d N Nc := fun tail =>
    (CMP99AnchoredWalk.toGeneralizedWalk
      (⟨n, tail⟩ : CMP99AnchoredWalk
        (cmp99PhysicalPatchSuccessorSteps charts core enlarged dist R)
        left)).term
      (cmp99PhysicalPatchHead charts K enlarged core hc hmass hK)
      (fun _ => cmp99PhysicalPatchContinuation
        charts K enlarged core hc hmass hK)
  calc
    (∑ word :
        ↥(cmp99PhysicalPatchHeadAnchoredAdmissibleWords
          charts core enlarged dist R left n),
      (cmp99SingleSpeciesWalk left word.1).term
        (cmp99PhysicalPatchHead charts K enlarged core hc hmass hK)
        (fun _ => cmp99PhysicalPatchContinuation
          charts K enlarged core hc hmass hK)) =
        ∑ word, f (e word) := by
          apply Finset.sum_congr rfl
          intro word _hword
          rfl
    _ = ∑ tail, f tail := e.sum_comp f

end

end YangMills.RG
