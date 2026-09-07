/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214PhysicalIndices
import YangMills.RG.BalabanCMP116SourceSigmaZeroActiveCarrier

/-!
# CMP116 equation (2.14): the literal physical gap carrier

The weakening derivatives in one localized equation-(2.14) term are indexed
by the block gap between the selected localization region `Z₀` and the
large-field union `Y₀(D)`.  This file records that carrier literally as

`Z₀ \ Y₀(D)`.

This is deliberately not identified with `Z₀`, with the canonical
localization core, or with the ambient weakening partition.  The elementary
inclusion into `Z₀` is nevertheless exactly the geometric fact needed to turn
the finite-rank determinant trace bound into a cost proportional to `|Z₀|`.
-/

namespace YangMills.RG

noncomputable section

/-- The literal CMP116 gap carrier `Z₀ \ Y₀(D)` for the weakening
coordinates of a localized equation-(2.14) term. -/
noncomputable def cmp116Eq214PhysicalGapCarrier
    {d M N' : ℕ} [NeZero M] [NeZero N']
    (D : Finset (Finset (FinBox d N')))
    (Z0 : Finset (FinBox d N')) : Finset (FinBox d N') :=
  Z0 \ cmp116Eq23Y0 D

@[simp] theorem mem_cmp116Eq214PhysicalGapCarrier_iff
    {d M N' : ℕ} [NeZero M] [NeZero N']
    {D : Finset (Finset (FinBox d N'))}
    {Z0 : Finset (FinBox d N')} {c : FinBox d N'} :
    c ∈ cmp116Eq214PhysicalGapCarrier (M := M) D Z0 ↔
      c ∈ Z0 ∧ c ∉ cmp116Eq23Y0 D := by
  simp [cmp116Eq214PhysicalGapCarrier]

/-- Every physical gap coordinate lies in its localization region. -/
theorem cmp116Eq214PhysicalGapCarrier_subset_Z0
    {d M N' : ℕ} [NeZero M] [NeZero N']
    (D : Finset (Finset (FinBox d N')))
    (Z0 : Finset (FinBox d N')) :
    cmp116Eq214PhysicalGapCarrier (M := M) D Z0 ⊆ Z0 := by
  exact Finset.sdiff_subset

/-- The physical gap is disjoint from the large-field union by
construction. -/
theorem cmp116Eq214PhysicalGapCarrier_disjoint_Y0
    {d M N' : ℕ} [NeZero M] [NeZero N']
    (D : Finset (Finset (FinBox d N')))
    (Z0 : Finset (FinBox d N')) :
    Disjoint (cmp116Eq214PhysicalGapCarrier (M := M) D Z0)
      (cmp116Eq23Y0 D) := by
  refine Finset.disjoint_left.2 ?_
  intro c hc hY0
  exact (mem_cmp116Eq214PhysicalGapCarrier_iff.mp hc).2 hY0

/-- If the distinguished source `Pi⁴` block domain is one of the selected
large-field domains, all of its blocks belong to `Y₀(D)`. -/
theorem cmp99SourcePi4LargeBlocks_subset_cmp116Eq23Y0_of_mem
    {Q : ℕ} [NeZero Q]
    (anchor : FinBox 4 Q)
    {D : Finset (Finset (FinBox 4 (2 * Q)))}
    (hPi4 :
      cmp99SourceDomainLargeBlocks (cmp99SourcePi4CollarDomain anchor) ∈ D) :
    cmp99SourceDomainLargeBlocks (cmp99SourcePi4CollarDomain anchor) ⊆
      cmp116Eq23Y0 D := by
  intro block hblock
  exact mem_cmp116Eq23Y0_iff.mpr
    ⟨cmp99SourceDomainLargeBlocks
      (cmp99SourcePi4CollarDomain anchor), hPi4, hblock⟩

/-- Once the distinguished `Pi⁴` domain is part of `Y₀(D)`, the literal
physical gap lies in the source weakening partition `sigma₀`.  This is the
exact set-theoretic bridge required by the restricted complex contour. -/
theorem cmp116Eq214PhysicalGapCarrier_subset_sigmaZero_of_pi4_mem
    {M Q : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (D : Finset (Finset (FinBox 4 (2 * Q))))
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (hPi4 :
      cmp99SourceDomainLargeBlocks (cmp99SourcePi4CollarDomain anchor) ∈ D) :
    cmp116Eq214PhysicalGapCarrier (M := M) D Z0 ⊆
      cmp116SourceSigmaZero anchor := by
  intro block hgap
  have hgap' := mem_cmp116Eq214PhysicalGapCarrier_iff.mp hgap
  have hnotPi4 :
      block ∉
        cmp99SourceDomainLargeBlocks
          (cmp99SourcePi4CollarDomain anchor) := by
    intro hblock
    exact hgap'.2
      (cmp99SourcePi4LargeBlocks_subset_cmp116Eq23Y0_of_mem
        anchor hPi4 hblock)
  simp [cmp116SourceSigmaZero, hnotPi4]

/-- A localization-admissible `Z₀` contains the complete large-field union
`Y₀(D)`. -/
theorem cmp116Eq23Y0_subset_of_localizationAdmissible
    {d M N' : ℕ} [NeZero M] [NeZero N']
    {D : Finset (Finset (FinBox d N'))}
    {P : Finset (PhysicalBond d (M * N'))}
    {Z0 : Finset (FinBox d N')}
    (hZ0 : CMP116LocalizationAdmissible D P Z0) :
    cmp116Eq23Y0 D ⊆ Z0 := by
  intro c hc
  exact hZ0.1 (cmp116Eq23Y0_subset_localizationSeed D P hc)

/-- For a localization-admissible region, the gap cardinality is exactly
`|Z₀| - |Y₀(D)|`. -/
theorem card_cmp116Eq214PhysicalGapCarrier_of_localizationAdmissible
    {d M N' : ℕ} [NeZero M] [NeZero N']
    {D : Finset (Finset (FinBox d N'))}
    {P : Finset (PhysicalBond d (M * N'))}
    {Z0 : Finset (FinBox d N')}
    (hZ0 : CMP116LocalizationAdmissible D P Z0) :
    (cmp116Eq214PhysicalGapCarrier (M := M) D Z0).card =
      Z0.card - (cmp116Eq23Y0 D).card := by
  rw [cmp116Eq214PhysicalGapCarrier,
    Finset.card_sdiff_of_subset
      (cmp116Eq23Y0_subset_of_localizationAdmissible hZ0)]

/-- A source-selected least localization region gives the same exact gap
cardinality without exposing its admissibility proof to downstream callers. -/
theorem card_cmp116Eq214PhysicalGapCarrier_of_mem_Eq214Z0Index
    {d M N' : ℕ} [NeZero M] [NeZero N']
    {allowed : Finset (Finset (FinBox d N'))}
    {Z : Finset (FinBox d N')}
    {D : Finset (Finset (FinBox d N'))}
    {P : Finset (PhysicalBond d (M * N'))}
    {Z0 : Finset (FinBox d N')}
    (hZ0 : Z0 ∈ cmp116Eq214Z0Index allowed Z D P) :
    (cmp116Eq214PhysicalGapCarrier (M := M) D Z0).card =
      Z0.card - (cmp116Eq23Y0 D).card := by
  rw [mem_cmp116Eq214Z0Index_iff] at hZ0
  exact
    card_cmp116Eq214PhysicalGapCarrier_of_localizationAdmissible
      hZ0.2.2.1

end

end YangMills.RG
