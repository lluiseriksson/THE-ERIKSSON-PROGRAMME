/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP109Lemma1CombinedCenteredRegion
import YangMills.RG.BalabanCMP109Lemma1Eq136SourceCertificate
import YangMills.RG.BalabanCMP116Eq222CutoffSupNormTransport

/-!
# The retracted all-interior cutoff carrier and its obstruction

An earlier attempted producer used the complete bilateral interior-bond
carrier of the combined centered region as one common small-field carrier.
That inference was too strong.  The primary statement (1.34) supplies a
per-domain analytic/locality obligation even though the reconstructed literal
residual contains the global correction `D(B)`; it does not identify the
small-field carrier with every bond of the later centered region `Z0`.

This file retains the exact diagnostics for that retracted construction:

* a nonzero small-field cutoff remains nonzero on every subcarrier;
* the direct equation-(80) source carrier is contained in the attempted
  all-interior carrier.

The formal transport lemmas below explain what a nonzero common cutoff would
control.  They do **not** prove that this support is inhabited.  In fact the
terminal no-go theorem records the decisive obstruction: the localization
core makes every selected large-field bond in `P` interior, so using all
interior bonds as the small-field carrier makes the signed cutoff identically
zero whenever `P` is nonempty.  The replacement source carrier is constructed
separately from the equation-(2.14) exterior carrier; this file must not be
used to inhabit a combined equation-(1.36) endpoint.
-/

namespace YangMills.RG

noncomputable section

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

/-- Conditional transport to the native CMP109 small-field predicate.  The
extra inclusion states explicitly that the individual native carrier lies in
the attempted all-interior carrier.  This implication remains diagnostic:
its cutoff premise is uninhabited for nonempty `P`. -/
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
    (Y : CMP116LocalizationDomain 2 (M * (2 * Q)))
    (hY : cmp109Lemma1SourceBondSupport Y ⊆
      PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds
        (cmp116Eq80Lemma1CombinedCenteredRegion anchor D E P)) :
    cmp109Lemma1SourceSmallField epsilon1 gk Y
      (physicalBondProjection
        (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds
          (cmp116Eq80Lemma1CombinedCenteredRegion anchor D E P))
        (cmp116SourcePhysicalCoordinateCochain b)) := by
  unfold cmp109Lemma1SourceSmallField
  have hprojection :
      physicalBondProjection (cmp109Lemma1SourceBondSupport Y)
          (physicalBondProjection
            (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds
              (cmp116Eq80Lemma1CombinedCenteredRegion anchor D E P))
            (cmp116SourcePhysicalCoordinateCochain b)) =
        physicalBondProjection (cmp109Lemma1SourceBondSupport Y)
          (cmp116SourcePhysicalCoordinateCochain b) := by
    have hcomp := congrArg
      (fun T => T (cmp116SourcePhysicalCoordinateCochain b))
      (physicalBondProjection_comp_of_subset_right (Nc := Nc) hY)
    simpa using hcomp
  rw [hprojection]
  exact
    cmp98SourceFieldSupNorm_physicalBondProjection_le_threshold_of_cutoffFactor_ne_zero
      (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds
        (cmp116Eq80Lemma1CombinedCenteredRegion anchor D E P))
      P
      (cmp109Lemma1SourceBondSupport Y)
      (epsilon1 / gk) b
      (div_nonneg hepsilon1 (le_of_lt hgk)) hY hcutoff

end

end YangMills.RG
