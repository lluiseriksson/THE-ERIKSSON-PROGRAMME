/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalSupNormTransport
import YangMills.RG.BalabanCMP116Eq222CutoffSupportInteraction
import YangMills.RG.BalabanCMP116SourcePhysicalBondField

/-!
# Transport the CMP116 cutoff support to the physical source sup norm

The equation-(2.14) Gaussian coordinate is unbounded, but the literal
small-field cutoff restricts its physical bond values on `Y0`.  A localized
CMP102/CMP116 activity only reads a subcarrier `S ⊆ Y0`; after projecting to
that carrier, its source-facing maximum norm is therefore bounded by the
printed cutoff threshold.

This is the missing norm-level consequence of cutoff support.  It deliberately
does **not** assert that all bonds in the localization hull `Z0` lie in `Y0`.
Installing equation (1.36) still requires the source dictionary proving that
each residual activity reads only a carrier contained in `Y0`.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No placeholders or
local axioms.
-/

namespace YangMills.RG

noncomputable section

/-- Nonvanishing of the small-field product descends to a subcarrier. -/
theorem cmp116SmallFieldCutoff_ne_zero_of_subset
    {Bond E : Type*} [DecidableEq Bond] [Norm E]
    {small large : Finset Bond} {threshold : ℝ} {B : Bond → E}
    (hsub : small ⊆ large)
    (hlarge : cmp116SmallFieldCutoff large threshold B ≠ 0) :
    cmp116SmallFieldCutoff small threshold B ≠ 0 := by
  unfold cmp116SmallFieldCutoff
  refine Finset.prod_ne_zero_iff.mpr fun bond hbond => ?_
  have hlt : ‖B bond‖ < threshold :=
    norm_lt_of_cmp116SmallFieldCutoff_ne_zero
      large threshold B hlarge (hsub hbond)
  simp [cmp116SmallFieldIndicator, hlt]

/-- The complete signed cutoff remains nonzero after restricting only its
small-field carrier.  The large-field set and its sign are unchanged. -/
theorem cmp116SignedCutoff_ne_zero_of_smallFieldCarrier_subset
    {Bond E : Type*} [DecidableEq Bond] [Norm E]
    {small large P : Finset Bond} {threshold : ℝ} {B : Bond → E}
    (hsub : small ⊆ large)
    (hcutoff :
      (-1 : ℂ) ^ P.card * cmp116SmallFieldCutoff large threshold B *
          cmp116LargeFieldCutoff P threshold B ≠ 0) :
    (-1 : ℂ) ^ P.card * cmp116SmallFieldCutoff small threshold B *
        cmp116LargeFieldCutoff P threshold B ≠ 0 := by
  have hsmallLarge : cmp116SmallFieldCutoff large threshold B ≠ 0 := by
    intro hzero
    apply hcutoff
    simp [hzero]
  have hP : cmp116LargeFieldCutoff P threshold B ≠ 0 := by
    intro hzero
    apply hcutoff
    simp [hzero]
  exact mul_ne_zero
    (mul_ne_zero (pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0))
      (cmp116SmallFieldCutoff_ne_zero_of_subset hsub hsmallLarge)) hP

/-- Pointwise cutoff control survives projection to any physical bond
subcarrier of `Y0`. -/
theorem norm_physicalBondProjection_cmp116SourcePhysicalCoordinateCochain_le_threshold
    {d M N' Nc : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    (Y0 S : Finset (PhysicalBond d (M * N')))
    (threshold : ℝ)
    (b : CMP116Eq214GaussianCoordinate
      (PhysicalBond d (M * N')) (Nc ^ 2 - 1))
    (hthreshold : 0 ≤ threshold)
    (hS : S ⊆ Y0)
    (hsmall :
      cmp116SmallFieldCutoff Y0 threshold
        (cmp116SourcePhysicalCoordinateCochain b) ≠ 0)
    (bond : PhysicalBond d (M * N')) :
    ‖physicalBondProjection S
        (cmp116SourcePhysicalCoordinateCochain b) bond‖ ≤ threshold := by
  by_cases hbond : bond ∈ S
  · rw [physicalBondProjection_apply_mem S hbond]
    exact le_of_lt
      (norm_lt_of_cmp116SmallFieldCutoff_ne_zero
        Y0 threshold (cmp116SourcePhysicalCoordinateCochain b)
        hsmall (hS hbond))
  · rw [physicalBondProjection_apply_not_mem S hbond, norm_zero]
    exact hthreshold

/-- The projected physical field has the source-facing, volume-uniform
sup norm bounded by the cutoff threshold. -/
theorem cmp98SourceFieldSupNorm_physicalBondProjection_le_threshold
    {d M N' Nc : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    (Y0 S : Finset (PhysicalBond d (M * N')))
    (threshold : ℝ)
    (b : CMP116Eq214GaussianCoordinate
      (PhysicalBond d (M * N')) (Nc ^ 2 - 1))
    (hthreshold : 0 ≤ threshold)
    (hS : S ⊆ Y0)
    (hsmall :
      cmp116SmallFieldCutoff Y0 threshold
        (cmp116SourcePhysicalCoordinateCochain b) ≠ 0) :
    cmp98SourceFieldSupNorm
        (physicalBondProjection S
          (cmp116SourcePhysicalCoordinateCochain b)) ≤ threshold := by
  unfold cmp98SourceFieldSupNorm
  apply Finset.max'_le
  intro value hvalue
  rcases Finset.mem_image.mp hvalue with ⟨bond, _, rfl⟩
  exact
    norm_physicalBondProjection_cmp116SourcePhysicalCoordinateCochain_le_threshold
      Y0 S threshold b hthreshold hS hsmall bond

/-- Nonvanishing of the complete signed CMP116 cutoff implies the same
sup-norm bound.  The large-field factor on `P` is used only to infer that the
small-field factor on `Y0` is nonzero. -/
theorem cmp98SourceFieldSupNorm_physicalBondProjection_le_threshold_of_cutoffFactor_ne_zero
    {d M N' Nc : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    (Y0 P S : Finset (PhysicalBond d (M * N')))
    (threshold : ℝ)
    (b : CMP116Eq214GaussianCoordinate
      (PhysicalBond d (M * N')) (Nc ^ 2 - 1))
    (hthreshold : 0 ≤ threshold)
    (hS : S ⊆ Y0)
    (hcutoff :
      (-1 : ℂ) ^ P.card *
          cmp116SmallFieldCutoff Y0 threshold
            (cmp116SourcePhysicalCoordinateCochain b) *
          cmp116LargeFieldCutoff P threshold
            (cmp116SourcePhysicalCoordinateCochain b) ≠ 0) :
    cmp98SourceFieldSupNorm
        (physicalBondProjection S
          (cmp116SourcePhysicalCoordinateCochain b)) ≤ threshold := by
  have hsmall :
      cmp116SmallFieldCutoff Y0 threshold
        (cmp116SourcePhysicalCoordinateCochain b) ≠ 0 := by
    intro hzero
    apply hcutoff
    simp [hzero]
  exact
    cmp98SourceFieldSupNorm_physicalBondProjection_le_threshold
      Y0 S threshold b hthreshold hS hsmall

/-- An additional coordinate projection cannot destroy cutoff control.  No
containment relation between the extra carrier `R` and the localized source
carrier `S` is required: coordinates outside `R` are simply zero. -/
theorem cmp98SourceFieldSupNorm_nestedPhysicalBondProjection_le_threshold_of_cutoffFactor_ne_zero
    {d M N' Nc : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    (Y0 P S R : Finset (PhysicalBond d (M * N')))
    (threshold : ℝ)
    (b : CMP116Eq214GaussianCoordinate
      (PhysicalBond d (M * N')) (Nc ^ 2 - 1))
    (hthreshold : 0 ≤ threshold)
    (hS : S ⊆ Y0)
    (hcutoff :
      (-1 : ℂ) ^ P.card *
          cmp116SmallFieldCutoff Y0 threshold
            (cmp116SourcePhysicalCoordinateCochain b) *
          cmp116LargeFieldCutoff P threshold
            (cmp116SourcePhysicalCoordinateCochain b) ≠ 0) :
    cmp98SourceFieldSupNorm
        (physicalBondProjection S
          (physicalBondProjection R
            (cmp116SourcePhysicalCoordinateCochain b))) ≤ threshold := by
  have hsmall :
      cmp116SmallFieldCutoff Y0 threshold
        (cmp116SourcePhysicalCoordinateCochain b) ≠ 0 := by
    intro hzero
    apply hcutoff
    simp [hzero]
  unfold cmp98SourceFieldSupNorm
  apply Finset.max'_le
  intro value hvalue
  rcases Finset.mem_image.mp hvalue with ⟨bond, _, rfl⟩
  by_cases hbondS : bond ∈ S
  · rw [physicalBondProjection_apply_mem S hbondS]
    by_cases hbondR : bond ∈ R
    · rw [physicalBondProjection_apply_mem R hbondR]
      exact le_of_lt
        (norm_lt_of_cmp116SmallFieldCutoff_ne_zero
          Y0 threshold (cmp116SourcePhysicalCoordinateCochain b)
          hsmall (hS hbondS))
    · rw [physicalBondProjection_apply_not_mem R hbondR, norm_zero]
      exact hthreshold
  · rw [physicalBondProjection_apply_not_mem S hbondS, norm_zero]
    exact hthreshold

end

end YangMills.RG
