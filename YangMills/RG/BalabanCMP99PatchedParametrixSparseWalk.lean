/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99PatchedParametrixTransitionSupport

/-!
# Sparse physical walks for the CMP99 patched parametrix

The raw noncommutative expansion of the patched inverse sums every ordered
chart word.  Exact transition support now removes every word containing a
range-separated consecutive pair.  The surviving words are defined by the
literal physical near-range relation, not by an assumed successor family.

The homogeneous layers and the complete corrected covariance are rewritten
as sums over these physically admissible words.  A uniform cardinal bound on
the surviving successor family still requires the concrete source chart
geometry and is not asserted here.
-/

open scoped BigOperators

namespace YangMills.RG

noncomputable section

universe u v

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- A generic ordered product vanishes when its word contains a forbidden
consecutive pair whose two operator factors multiply to zero. -/
theorem list_map_prod_eq_zero_of_not_chain'
    {ι : Type u} {E : Type v} [MonoidWithZero E]
    (near : ι → ι → Prop) (R : ι → E)
    (hzero : ∀ left right, ¬ near left right → R left * R right = 0) :
    ∀ word : List ι, ¬ word.IsChain near → (word.map R).prod = 0 := by
  intro word
  induction word with
  | nil =>
      intro hnot
      exact (hnot (by simp)).elim
  | cons left tail ih =>
      cases tail with
      | nil =>
          intro hnot
          exact (hnot (by simp)).elim
      | cons right rest =>
          intro hnot
          by_cases hnear : near left right
          · have htail : ¬ (right :: rest).IsChain near := by
              intro hchain
              exact hnot ((List.isChain_cons_cons).mpr ⟨hnear, hchain⟩)
            have hz := ih htail
            simp only [List.map_cons, List.prod_cons] at hz ⊢
            rw [hz, mul_zero]
          · simp only [List.map_cons, List.prod_cons]
            rw [← mul_assoc, hzero left right hnear, zero_mul]

/-- The physical successor relation retained by exact finite-range support.
`right` can follow `left` precisely when their core/enlarged carriers are not
range-separated. -/
def CMP99PhysicalPatchCanFollow
    {ι : Type*}
    {d N : ℕ} [NeZero N]
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (R : ℕ)
    (left right : ι) : Prop :=
  ¬CMP99PhysicalRangeSeparated dist R (core left) (enlarged right)

/-- The finite family of physical charts that can follow a fixed chart. -/
noncomputable def cmp99PhysicalPatchSuccessors
    {ι : Type*} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (R : ℕ)
    (left : ↥charts) : Finset ↥charts :=
  by
    classical
    exact Finset.univ.filter fun right =>
      CMP99PhysicalPatchCanFollow core enlarged dist R left right

@[simp]
theorem mem_cmp99PhysicalPatchSuccessors_iff
    {ι : Type*} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (R : ℕ)
    (left right : ↥charts) :
    right ∈ cmp99PhysicalPatchSuccessors charts core enlarged dist R left ↔
      CMP99PhysicalPatchCanFollow core enlarged dist R left right := by
  simp [cmp99PhysicalPatchSuccessors]

/-- Ordered chart tuples whose every consecutive transition survives the
exact physical range test. -/
noncomputable def cmp99PhysicalPatchAdmissibleWords
    {ι : Type*} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (R n : ℕ) :
    Finset (Fin n → ↥charts) :=
  by
    classical
    exact Finset.univ.filter fun word =>
      (List.ofFn word).IsChain
        (fun left right : ↥charts =>
          CMP99PhysicalPatchCanFollow core enlarged dist R left right)

/-- Every physically inadmissible continuation tuple has exactly zero ordered
operator product. -/
theorem cmp99OrderedTupleProduct_physicalContinuation_eq_zero_of_not_admissible
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
    {n : ℕ} (word : Fin n → ↥charts)
    (hnot : ¬(List.ofFn word).IsChain
      (fun left right : ↥charts =>
        CMP99PhysicalPatchCanFollow core enlarged dist R left right)) :
    cmp99OrderedTupleProduct
        (cmp99PhysicalPatchContinuation
          charts K enlarged core hc hmass hK) word = 0 := by
  rw [cmp99OrderedTupleProduct]
  apply list_map_prod_eq_zero_of_not_chain'
    (fun left right : ↥charts =>
      CMP99PhysicalPatchCanFollow core enlarged dist R left right)
    (cmp99PhysicalPatchContinuation charts K enlarged core hc hmass hK)
  · intro left right hnotNear
    have hsep :
        CMP99PhysicalRangeSeparated dist R (core left) (enlarged right) := by
      simpa [CMP99PhysicalPatchCanFollow] using hnotNear
    exact cmp99PhysicalPatchContinuation_mul_eq_zero_of_rangeSeparated
      charts K enlarged core hsub dist hrange hc hmass hK left right hsep
  · exact hnot

/-- The exact degree-`n` patched layer is the sum over physically admissible
chart words only. -/
theorem cmp99PatchedPhysicalParametrix_mul_neg_defect_pow_eq_sparse_walk_sum
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι)
    (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    (hsub : ∀ i, i ∈ charts → core i ⊆ enlarged i)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) {R : ℕ}
    (hrange : PhysicalCovarianceFiniteRange K dist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) (n : ℕ) :
    cmp99PatchedPhysicalParametrix charts K enlarged core hc hmass hK *
        (-cmp99PatchedPhysicalParametrixDefect
          charts K enlarged core hc hmass hK) ^ n =
      ∑ head : ↥charts,
        ∑ word ∈ cmp99PhysicalPatchAdmissibleWords
            charts core enlarged dist R n,
          (cmp99SingleSpeciesWalk head word).term
            (cmp99PhysicalPatchHead charts K enlarged core hc hmass hK)
            (fun _ => cmp99PhysicalPatchContinuation
              charts K enlarged core hc hmass hK) := by
  classical
  rw [cmp99PatchedPhysicalParametrix_mul_neg_defect_pow_eq_walk_sum]
  apply Finset.sum_congr rfl
  intro head _hhead
  symm
  rw [cmp99PhysicalPatchAdmissibleWords]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro word _hword hnotMem
  have hnot : ¬(List.ofFn word).IsChain
      (fun left right : ↥charts =>
        CMP99PhysicalPatchCanFollow core enlarged dist R left right) := by
    simpa using hnotMem
  rw [cmp99SingleSpeciesWalk_term,
    cmp99OrderedTupleProduct_physicalContinuation_eq_zero_of_not_admissible
      charts K enlarged core hsub dist hrange hc hmass hK word hnot,
    mul_zero]

/-- The complete corrected covariance is the countable sum of the sparse
physical walk layers. -/
theorem cmp99CorrectedPatchedPhysicalCovariance_eq_tsum_sparse_walk_layers
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
    (hD : ‖cmp99PatchedPhysicalParametrixDefect
      charts K enlarged core hc hmass hK‖ < 1) :
    cmp99CorrectedPatchedPhysicalCovariance
        charts K enlarged core hc hmass hK =
      ∑' n : ℕ, ∑ head : ↥charts,
        ∑ word ∈ cmp99PhysicalPatchAdmissibleWords
            charts core enlarged dist R n,
          (cmp99SingleSpeciesWalk head word).term
            (cmp99PhysicalPatchHead charts K enlarged core hc hmass hK)
            (fun _ => cmp99PhysicalPatchContinuation
              charts K enlarged core hc hmass hK) := by
  rw [cmp99CorrectedPatchedPhysicalCovariance_eq_tsum_walk_layers
    charts K enlarged core hc hmass hK hD]
  apply tsum_congr
  intro n
  exact
    (cmp99PatchedPhysicalParametrix_mul_neg_defect_pow_eq_walk_sum
      charts K enlarged core hc hmass hK n).symm.trans
      (cmp99PatchedPhysicalParametrix_mul_neg_defect_pow_eq_sparse_walk_sum
        charts K enlarged core hsub dist hrange hc hmass hK n)

end

end YangMills.RG
