/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP109Lemma1CombinedCenteredRegion
import YangMills.RG.BalabanCMP109Lemma1Eq136SourceCertificate
import YangMills.RG.BalabanCMP116Eq222CutoffSupNormTransport

/-!
# One cutoff carrier for the direct and Lemma-1 residual sectors

The direct equation-(80) residual is localized to its source domains, while
the native CMP109 Lemma-1 residual contains the global correction `D(B)`.
Consequently the terminal cutoff carrier cannot be reduced to a native
domain bond support.  The honest common choice is the complete bilateral
interior-bond carrier of the combined centered region.

This file proves two facts needed by the combined equation-(1.36) producer:

* a nonzero small-field cutoff remains nonzero on every subcarrier;
* the direct equation-(80) source carrier is contained in the common
  interior-bond carrier.

Thus one terminal cutoff controls the full projected field used by Lemma-1
and, by restriction, supplies the already-proved direct equation-(80) bound.
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

/-- Every bond in the literal direct equation-(80) source carrier is
bilaterally interior to the combined direct/native centered region. -/
theorem cmp102Eq80SourcePi4PhysicalY0_subset_combinedRegionInterior
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (P : Finset (PhysicalBond 4 (M * (2 * Q)))) :
    cmp102Eq80SourcePi4PhysicalY0 (M := M) anchor D ⊆
      PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds
        (cmp116Eq80Lemma1CombinedCenteredRegion anchor D E P) := by
  intro bond hbond
  unfold cmp102Eq80SourcePi4PhysicalY0 at hbond
  rw [mem_cmp116Eq23Y0_iff] at hbond
  rcases hbond with ⟨S, hS, hbond⟩
  rcases Finset.mem_image.mp hS with ⟨W, hWD, rfl⟩
  have hold :=
    cmp102Eq80SourcePi4LocalizationDomain_bondSupport_subset_centeredRegionInterior
      anchor D P W hWD hbond
  rw [PhysicalGaugeCMP116Dictionary.mem_cmp116Eq223PhysicalInteriorBonds_iff]
    at hold ⊢
  rw [cmp116BondInterior_iff_blocks_subset] at hold ⊢
  intro c hc
  exact cmp102Eq80SourcePi4CenteredRegion_subset_combinedCenteredRegion
    anchor D E P (hold hc)

/-- Projecting first to the combined centered region and then to a direct
source domain is exactly the direct source-domain projection. -/
theorem physicalBondProjection_indexedSourceDomain_combinedCenteredRegion
    {Index : Type*} {M Q Nc L lieDim : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    [NeZero Nc] [NeZero (Nc ^ 2 - 1)] [NeZero L] [NeZero lieDim]
    (Dict : PhysicalGaugeCMP116Dictionary
      4 (M * (2 * Q)) Nc 4 L lieDim)
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (P : Finset (PhysicalBond 4 (M * (2 * Q))))
    (i : Fin (CMP102Eq80SourcePi4DomainCount anchor D))
    (A : PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc) :
    let Y := cmp102Eq80SourcePi4IndexedLocalizationDomain
      (M := M) anchor D i
    let Z0 := cmp116Eq80Lemma1CombinedCenteredRegion anchor D E P
    physicalBondProjection Y.bondSupport
        (physicalBondProjection
          (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
          A) =
      physicalBondProjection Y.bondSupport A := by
  dsimp only
  apply PiLp.ext
  intro bond
  by_cases hbond : bond ∈
      (cmp102Eq80SourcePi4IndexedLocalizationDomain
        (M := M) anchor D i).bondSupport
  · have hinterior :
        bond ∈
          PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds
            (cmp116Eq80Lemma1CombinedCenteredRegion anchor D E P) :=
      cmp102Eq80SourcePi4IndexedLocalizationDomain_bondSupport_subset_combinedRegionInterior
        anchor D E P i hbond
    simp [physicalBondProjection_apply_mem, hbond, hinterior]
  · simp [physicalBondProjection_apply_not_mem, hbond]

/-- A nonzero cutoff on the common interior carrier supplies the literal
direct equation-(80) cutoff without changing the large-field factor. -/
theorem cmp116DirectSignedCutoff_ne_zero_of_combinedInteriorCutoff
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (P : Finset (PhysicalBond 4 (M * (2 * Q))))
    (threshold : ℝ)
    (b : CMP116Eq214GaussianCoordinate
      (PhysicalBond 4 (M * (2 * Q))) (Nc ^ 2 - 1))
    (hcutoff :
      (-1 : ℂ) ^ P.card *
          cmp116SmallFieldCutoff
            (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds
              (cmp116Eq80Lemma1CombinedCenteredRegion anchor D E P))
            threshold (cmp116SourcePhysicalCoordinateCochain b) *
          cmp116LargeFieldCutoff P threshold
            (cmp116SourcePhysicalCoordinateCochain b) ≠ 0) :
    (-1 : ℂ) ^ P.card *
          cmp116SmallFieldCutoff
            (cmp102Eq80SourcePi4PhysicalY0 (M := M) anchor D)
            threshold (cmp116SourcePhysicalCoordinateCochain b) *
          cmp116LargeFieldCutoff P threshold
            (cmp116SourcePhysicalCoordinateCochain b) ≠ 0 := by
  exact cmp116SignedCutoff_ne_zero_of_smallFieldCarrier_subset
    (cmp102Eq80SourcePi4PhysicalY0_subset_combinedRegionInterior
      anchor D E P) hcutoff

/-- The enlarged common cutoff controls the same literal physical bond field
installed by `withSourcePhysicalBondField`.  Thus enlarging the terminal
carrier does not decouple the cutoff from the field used by the energy and
cubic-residual producers. -/
theorem norm_cmp116SourcePhysicalCoordinateCochain_lt_of_combinedInteriorCutoff
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (P : Finset (PhysicalBond 4 (M * (2 * Q))))
    (threshold : ℝ)
    (b : CMP116Eq214GaussianCoordinate
      (PhysicalBond 4 (M * (2 * Q))) (Nc ^ 2 - 1))
    (hcutoff :
      (-1 : ℂ) ^ P.card *
          cmp116SmallFieldCutoff
            (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds
              (cmp116Eq80Lemma1CombinedCenteredRegion anchor D E P))
            threshold (cmp116SourcePhysicalCoordinateCochain b) *
          cmp116LargeFieldCutoff P threshold
            (cmp116SourcePhysicalCoordinateCochain b) ≠ 0)
    {bond : PhysicalBond 4 (M * (2 * Q))}
    (hbond : bond ∈
      PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds
        (cmp116Eq80Lemma1CombinedCenteredRegion anchor D E P)) :
    ‖cmp116SourcePhysicalCoordinateCochain b bond‖ < threshold := by
  have hsmall :
      cmp116SmallFieldCutoff
          (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds
            (cmp116Eq80Lemma1CombinedCenteredRegion anchor D E P))
          threshold (cmp116SourcePhysicalCoordinateCochain b) ≠ 0 := by
    intro hzero
    apply hcutoff
    simp [hzero]
  exact norm_lt_of_cmp116SmallFieldCutoff_ne_zero
    _ threshold (cmp116SourcePhysicalCoordinateCochain b) hsmall hbond

/-- On the same cutoff support, the full field projected to the combined
interior lies in the native CMP109 small-field region.  This controls the
global correction `D(P_Z0 B)` without claiming domain-locality of `D`. -/
theorem cmp109Lemma1SourceSmallField_combinedInteriorProjection_of_cutoff
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (P : Finset (PhysicalBond 4 (M * (2 * Q))))
    (epsilon1 gk : ℝ) (hepsilon1 : 0 ≤ epsilon1) (hgk : 0 < gk)
    (b : CMP116Eq214GaussianCoordinate
      (PhysicalBond 4 (M * (2 * Q))) (Nc ^ 2 - 1))
    (hcutoff :
      (-1 : ℂ) ^ P.card *
          cmp116SmallFieldCutoff
            (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds
              (cmp116Eq80Lemma1CombinedCenteredRegion anchor D E P))
            (epsilon1 / gk) (cmp116SourcePhysicalCoordinateCochain b) *
          cmp116LargeFieldCutoff P (epsilon1 / gk)
            (cmp116SourcePhysicalCoordinateCochain b) ≠ 0)
    (Y : CMP116LocalizationDomain 2 (M * (2 * Q))) :
    cmp109Lemma1SourceSmallField epsilon1 gk Y
      (physicalBondProjection
        (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds
          (cmp116Eq80Lemma1CombinedCenteredRegion anchor D E P))
        (cmp116SourcePhysicalCoordinateCochain b)) := by
  unfold cmp109Lemma1SourceSmallField
  exact
    cmp98SourceFieldSupNorm_physicalBondProjection_le_threshold_of_cutoffFactor_ne_zero
      (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds
        (cmp116Eq80Lemma1CombinedCenteredRegion anchor D E P))
      P
      (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds
        (cmp116Eq80Lemma1CombinedCenteredRegion anchor D E P))
      (epsilon1 / gk) b
      (div_nonneg hepsilon1 (le_of_lt hgk)) (fun _ h => h) hcutoff

end

end YangMills.RG
