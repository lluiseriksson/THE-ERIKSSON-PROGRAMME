/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq234GapSubsetSum

/-!
# Physical gap dictionary for CMP116 equation (2.34)

For a fixed source polymer `Z`, every admissible `Z0'` is a subregion of
`Z`.  Its gap is therefore the literal relative complement `Z \ Z0'`.
Relative complementation is injective on subregions of `Z`, and multiplying
the gap cardinality by the fourth power of the localization scale gives the
source normalization used in equation (2.26).

This module constructs `CMP116Eq234GapIndexEncoding` from those physical
objects.  No abstract injection or normalized-cardinality equality remains
to be supplied once the source index consists of subregions of `Z`.
-/

namespace YangMills.RG

noncomputable section

/-- Fine-volume cardinality corresponding to a coarse gap subset. -/
def cmp116Eq234PhysicalGapCard
    {α : Type*} [DecidableEq α]
    (localizationScale : ℕ) (Z Z0' : Finset α) : ℕ :=
  localizationScale ^ 4 * (Z \ Z0').card

namespace CMP116Eq234GapIndexEncoding

/-- Relative complementation by `Z` is injective on any source index whose
members are all contained in `Z`. -/
theorem physicalGap_injOn
    {α : Type*} [DecidableEq α]
    (Z : Finset α)
    (index : Finset (Finset α))
    (hsub : ∀ Z0' ∈ index, Z0' ⊆ Z) :
    Set.InjOn (fun Z0' : Finset α => Z \ Z0') index := by
  intro A hA B hB hgap
  change Z \ A = Z \ B at hgap
  apply Finset.Subset.antisymm
  · intro x hxA
    by_contra hxB
    have hxGapB : x ∈ Z \ B :=
      Finset.mem_sdiff.mpr ⟨hsub A hA hxA, hxB⟩
    rw [← hgap] at hxGapB
    exact (Finset.mem_sdiff.mp hxGapB).2 hxA
  · intro x hxB
    by_contra hxA
    have hxGapA : x ∈ Z \ A :=
      Finset.mem_sdiff.mpr ⟨hsub B hB hxB, hxA⟩
    rw [hgap] at hxGapA
    exact (Finset.mem_sdiff.mp hxGapA).2 hxB

/-- Exact fourth-power normalization of the physical gap cardinality. -/
theorem physicalGap_normalized
    {α : Type*} [DecidableEq α]
    (localizationScale : ℕ) [NeZero localizationScale]
    (Z Z0' : Finset α) :
    ((((localizationScale : ℝ) ^ 4)⁻¹) *
        (cmp116Eq234PhysicalGapCard
          localizationScale Z Z0' : ℝ)) =
      ((Z \ Z0').card : ℝ) := by
  have hscale : (localizationScale : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne localizationScale)
  have hpow : (localizationScale : ℝ) ^ 4 ≠ 0 :=
    pow_ne_zero 4 hscale
  unfold cmp116Eq234PhysicalGapCard
  simp only [Nat.cast_mul, Nat.cast_pow]
  rw [← mul_assoc, inv_mul_cancel₀ hpow, one_mul]

/-- Canonical equation-(2.34) encoding of a physical family of `Z0'`
subregions by their literal gaps inside `Z`. -/
def of_physicalSubregions
    {α : Type*} [DecidableEq α]
    (localizationScale : ℕ) [NeZero localizationScale]
    (Z : Finset α)
    (index : Finset (Finset α))
    (hsub : ∀ Z0' ∈ index, Z0' ⊆ Z) :
    CMP116Eq234GapIndexEncoding
      α index
      (cmp116Eq234PhysicalGapCard localizationScale Z)
      localizationScale where
  carrier := Z
  gapOf := fun Z0' => Z \ Z0'
  gap_subset := fun _Z0' _hZ0' => Finset.sdiff_subset
  gap_injective := physicalGap_injOn Z index hsub
  normalized_gap := fun Z0' _hZ0' =>
    physicalGap_normalized localizationScale Z Z0'

@[simp] theorem of_physicalSubregions_carrier
    {α : Type*} [DecidableEq α]
    (localizationScale : ℕ) [NeZero localizationScale]
    (Z : Finset α)
    (index : Finset (Finset α))
    (hsub : ∀ Z0' ∈ index, Z0' ⊆ Z) :
    (of_physicalSubregions localizationScale Z index hsub).carrier = Z :=
  rfl

@[simp] theorem of_physicalSubregions_gapOf
    {α : Type*} [DecidableEq α]
    (localizationScale : ℕ) [NeZero localizationScale]
    (Z : Finset α)
    (index : Finset (Finset α))
    (hsub : ∀ Z0' ∈ index, Z0' ⊆ Z)
    (Z0' : Finset α) :
    (of_physicalSubregions
      localizationScale Z index hsub).gapOf Z0' = Z \ Z0' :=
  rfl

end CMP116Eq234GapIndexEncoding

end

end YangMills.RG
