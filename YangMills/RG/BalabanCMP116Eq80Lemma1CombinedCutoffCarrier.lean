/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP109Lemma1CombinedCenteredRegion
import YangMills.RG.BalabanCMP109Lemma1Eq136SourceCertificate
import YangMills.RG.BalabanCMP116Eq222CutoffSupNormTransport

/-!
# The attempted common cutoff carrier and its obstruction

The direct equation-(80) residual is localized to its source domains, while
the native CMP109 Lemma-1 residual contains the global correction `D(B)`.
Consequently the terminal cutoff carrier cannot be reduced to a native
domain bond support.  The honest common choice is the complete bilateral
interior-bond carrier of the combined centered region.

This file proves two facts needed by the combined equation-(1.36) producer:

* a nonzero small-field cutoff remains nonzero on every subcarrier;
* the direct equation-(80) source carrier is contained in the common
  interior-bond carrier.

The formal transport lemmas below explain what a nonzero common cutoff would
control.  They do **not** prove that this support is inhabited.  In fact the
terminal no-go theorem records the decisive obstruction: the localization
core makes every selected large-field bond in `P` interior, so using all
interior bonds as the small-field carrier makes the signed cutoff identically
zero whenever `P` is nonempty.
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

/-- A bond cannot simultaneously belong to the strict small-field carrier and
the complementary large-field carrier.  This is the generic non-vacuity guard
that a proposed equation-(2.14) cutoff must pass. -/
theorem cmp116SignedCutoff_eq_zero_of_mem_small_and_large
    {Bond E : Type*} [DecidableEq Bond] [Norm E]
    {small P : Finset Bond} {threshold : ℝ} {B : Bond → E}
    {bond : Bond} (hsmall : bond ∈ small) (hlarge : bond ∈ P) :
    (-1 : ℂ) ^ P.card * cmp116SmallFieldCutoff small threshold B *
        cmp116LargeFieldCutoff P threshold B = 0 := by
  by_cases hlt : ‖B bond‖ < threshold
  · have hindicator : cmp116LargeFieldIndicator threshold (B bond) = 0 := by
      simp [cmp116LargeFieldIndicator, not_le_of_gt hlt]
    have hcutoff : cmp116LargeFieldCutoff P threshold B = 0 := by
      unfold cmp116LargeFieldCutoff
      exact Finset.prod_eq_zero hlarge hindicator
    simp [hcutoff]
  · have hindicator : cmp116SmallFieldIndicator threshold (B bond) = 0 := by
      simp [cmp116SmallFieldIndicator, hlt]
    have hcutoff : cmp116SmallFieldCutoff small threshold B = 0 := by
      unfold cmp116SmallFieldCutoff
      exact Finset.prod_eq_zero hsmall hindicator
    simp [hcutoff]

/-- The proposed all-interior common small-field carrier is incompatible with
every nonempty `P`: `cmp116LocalizationCore` deliberately makes each bond of
`P` interior.  Hence the combined signed cutoff used by the retracted
equation-(1.36) endpoint is identically zero for nonempty `P`. -/
theorem cmp116Eq80Lemma1CombinedInteriorSignedCutoff_eq_zero
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (P : Finset (PhysicalBond 4 (M * (2 * Q))))
    (threshold : ℝ)
    (B : PhysicalBond 4 (M * (2 * Q)) → SUNLieCoord Nc)
    (hP : P.Nonempty) :
    (-1 : ℂ) ^ P.card *
        cmp116SmallFieldCutoff
          (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds
            (cmp116Eq80Lemma1CombinedCenteredRegion anchor D E P))
          threshold B * cmp116LargeFieldCutoff P threshold B = 0 := by
  rcases hP with ⟨bond, hbond⟩
  apply cmp116SignedCutoff_eq_zero_of_mem_small_and_large
    (bond := bond) (hlarge := hbond)
  rw [PhysicalGaugeCMP116Dictionary.mem_cmp116Eq223PhysicalInteriorBonds_iff]
  exact cmp116BondInterior_localizationCore
    (cmp116Eq80Lemma1CombinedBlockDomainFamily anchor D E)
    (Finset.mem_union_left _ hbond)

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

/-- Conditional transport to the literal physical bond field.  This implication
must not be read as an inhabitation result: the terminal no-go theorem above
shows its premise is false for nonempty `P`. -/
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

/-- Conditional transport to the native CMP109 small-field predicate.  It is
formally useful for diagnosing the attempted construction, but its cutoff
premise is uninhabited for nonempty `P`. -/
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
