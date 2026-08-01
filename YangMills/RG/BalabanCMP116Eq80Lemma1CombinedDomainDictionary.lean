/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP109Lemma1CombinedCenteredRegion

/-!
# Canonical direct/native CMP116 domain dictionary

The centered terminal source uses one `Fin nY` index type for every residual
domain.  This module appends, without quotienting, the canonical equation-(80)
indices and the canonical native CMP109 Lemma-1 indices.  Its support and
metric dictionaries reduce literally on the two branches.

The common centered region constructed in the preceding module contains both
families, so the combined dictionary discharges `domain_nonempty` and
`domain_subset`.  Coincident native supports remain distinct indices and keep
their native metrics and native cardinalities.  This file does not sum the
two rooted estimates and does not claim `volume_budget` or a terminal
`TermSource`.
-/

namespace YangMills.RG

noncomputable section

/-- Canonical terminal domain count: selected direct domains followed by all
literal native Lemma-1 domains. -/
abbrev CMP116Eq80Lemma1CombinedDomainCount
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc) : ℕ :=
  CMP102Eq80SourcePi4DomainCount anchor D +
    CMP109Lemma1NativeDomainCount E

/-- Support dictionary on the disjoint direct/native index ledger. -/
noncomputable def cmp116Eq80Lemma1CombinedDomainSupport
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc) :
    Fin (CMP116Eq80Lemma1CombinedDomainCount anchor D E) →
      Finset (FinBox 4 (2 * Q)) :=
  Fin.append
    (fun i =>
      (cmp102Eq80SourcePi4IndexedLocalizationDomain
        (M := M) anchor D i).blocks)
    (cmp109Lemma1NativeIndexedDomainSupport E)

/-- Native tree metrics are retained; no metric is recomputed from the
coarsened support. -/
noncomputable def cmp116Eq80Lemma1CombinedDomainMetric
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc) :
    Fin (CMP116Eq80Lemma1CombinedDomainCount anchor D E) → ℕ :=
  Fin.append
    (cmp102Eq80SourcePi4IndexedDomainMetricNat (M := M) anchor D)
    (cmp109Lemma1NativeIndexedDomainMetric E)

/-- Literal normalized block cardinalities `M⁻⁴ |Y|` on the same disjoint
direct/native ledger.  The native branch is measured before support
coarsification. -/
noncomputable def cmp116Eq80Lemma1CombinedDomainCard
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc) :
    Fin (CMP116Eq80Lemma1CombinedDomainCount anchor D E) → ℕ :=
  Fin.append
    (cmp102Eq80SourcePi4IndexedDomainCard (M := M) anchor D)
    (cmp109Lemma1NativeIndexedDomainCard E)

@[simp] theorem cmp116Eq80Lemma1CombinedDomainSupport_direct
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (i : Fin (CMP102Eq80SourcePi4DomainCount anchor D)) :
    cmp116Eq80Lemma1CombinedDomainSupport anchor D E
        (Fin.castAdd (CMP109Lemma1NativeDomainCount E) i) =
      (cmp102Eq80SourcePi4IndexedLocalizationDomain
        (M := M) anchor D i).blocks := by
  simp [cmp116Eq80Lemma1CombinedDomainSupport]

@[simp] theorem cmp116Eq80Lemma1CombinedDomainSupport_native
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (i : Fin (CMP109Lemma1NativeDomainCount E)) :
    cmp116Eq80Lemma1CombinedDomainSupport anchor D E
        (Fin.natAdd (CMP102Eq80SourcePi4DomainCount anchor D) i) =
      cmp109Lemma1NativeIndexedDomainSupport E i := by
  simp [cmp116Eq80Lemma1CombinedDomainSupport]

@[simp] theorem cmp116Eq80Lemma1CombinedDomainMetric_direct
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (i : Fin (CMP102Eq80SourcePi4DomainCount anchor D)) :
    cmp116Eq80Lemma1CombinedDomainMetric anchor D E
        (Fin.castAdd (CMP109Lemma1NativeDomainCount E) i) =
      cmp102Eq80SourcePi4IndexedDomainMetricNat (M := M) anchor D i := by
  simp [cmp116Eq80Lemma1CombinedDomainMetric]

@[simp] theorem cmp116Eq80Lemma1CombinedDomainMetric_native
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (i : Fin (CMP109Lemma1NativeDomainCount E)) :
    cmp116Eq80Lemma1CombinedDomainMetric anchor D E
        (Fin.natAdd (CMP102Eq80SourcePi4DomainCount anchor D) i) =
      cmp109Lemma1NativeIndexedDomainMetric E i := by
  simp [cmp116Eq80Lemma1CombinedDomainMetric]

@[simp] theorem cmp116Eq80Lemma1CombinedDomainCard_direct
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (i : Fin (CMP102Eq80SourcePi4DomainCount anchor D)) :
    cmp116Eq80Lemma1CombinedDomainCard anchor D E
        (Fin.castAdd (CMP109Lemma1NativeDomainCount E) i) =
      cmp102Eq80SourcePi4IndexedDomainCard (M := M) anchor D i := by
  simp [cmp116Eq80Lemma1CombinedDomainCard]

@[simp] theorem cmp116Eq80Lemma1CombinedDomainCard_native
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (i : Fin (CMP109Lemma1NativeDomainCount E)) :
    cmp116Eq80Lemma1CombinedDomainCard anchor D E
        (Fin.natAdd (CMP102Eq80SourcePi4DomainCount anchor D) i) =
      cmp109Lemma1NativeIndexedDomainCard E i := by
  simp [cmp116Eq80Lemma1CombinedDomainCard]

/-- The terminal real-valued metric nonnegativity field is automatic for the
literal natural source metrics; no analytic decay hypothesis is used. -/
theorem cmp116Eq80Lemma1CombinedDomainMetric_nonneg
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc) :
    ∀ Y : Fin (CMP116Eq80Lemma1CombinedDomainCount anchor D E),
      0 ≤ (cmp116Eq80Lemma1CombinedDomainMetric anchor D E Y : ℝ) := by
  intro Y
  exact Nat.cast_nonneg _

/-- Every direct indexed block carrier is one of the generators of the
common localization core. -/
theorem cmp102Eq80SourcePi4IndexedDomainBlocks_subset_combinedCenteredRegion
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (P : Finset (PhysicalBond 4 (M * (2 * Q))))
    (i : Fin (CMP102Eq80SourcePi4DomainCount anchor D)) :
    (cmp102Eq80SourcePi4IndexedLocalizationDomain
        (M := M) anchor D i).blocks ⊆
      cmp116Eq80Lemma1CombinedCenteredRegion anchor D E P := by
  intro c hc
  apply cmp116LocalizationSeed_subset_core
  apply cmp116Eq23Y0_subset_localizationSeed
  apply mem_cmp116Eq23Y0_iff.mpr
  refine ⟨
    (cmp102Eq80SourcePi4IndexedLocalizationDomain
      (M := M) anchor D i).blocks, ?_, hc⟩
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  exact ⟨cmp102Eq80SourcePi4DomainAt anchor D i,
    cmp102Eq80SourcePi4DomainAt_mem anchor D i, rfl⟩

/-- The combined direct/native support dictionary is nowhere empty. -/
theorem cmp116Eq80Lemma1CombinedDomainSupport_nonempty
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc) :
    ∀ Y : Fin (CMP116Eq80Lemma1CombinedDomainCount anchor D E),
      (cmp116Eq80Lemma1CombinedDomainSupport anchor D E Y).Nonempty := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_)
  · simpa using
      (cmp102Eq80SourcePi4IndexedLocalizationDomain
        (M := M) anchor D i).nonempty
  · simpa using cmp109Lemma1NativeIndexedDomainSupport_nonempty E i

/-- Exact terminal `domain_subset` geometry for the appended dictionary. -/
theorem cmp116Eq80Lemma1CombinedDomainSupport_subset_combinedCenteredRegion
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (P : Finset (PhysicalBond 4 (M * (2 * Q)))) :
    ∀ Y : Fin (CMP116Eq80Lemma1CombinedDomainCount anchor D E),
      cmp116Eq80Lemma1CombinedDomainSupport anchor D E Y ⊆
        cmp116Eq80Lemma1CombinedCenteredRegion anchor D E P := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_)
  · simpa using
      cmp102Eq80SourcePi4IndexedDomainBlocks_subset_combinedCenteredRegion
        anchor D E P i
  · simpa using
      cmp109Lemma1NativeIndexedDomainSupport_subset_combinedCenteredRegion
        anchor D E P i

end

end YangMills.RG
