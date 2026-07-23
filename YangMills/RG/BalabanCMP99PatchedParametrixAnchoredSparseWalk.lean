/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99PatchedParametrixSparseWalk

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

end

end YangMills.RG
