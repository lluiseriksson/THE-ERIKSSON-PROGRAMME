/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq80Lemma1CombinedDomainDictionary
import YangMills.RG.BalabanCMP109Lemma1NativeRootedResidual
import YangMills.RG.BalabanCMP102Eq80SourcePi4RootedResidual

/-!
# Direct/native rooted residual composition

This module splits the terminal rooted residual sum along the canonical
direct/native `Fin.append` dictionary.  The native summand is discharged by
the physical CMP109 animal estimate.  The only remaining analytic input is a
rooted estimate for the direct equation-(80) family itself.

The resulting common bound is definitionally the sum of the two sector
bounds.  It is not defined as a supremum of the terminal left-hand side.  No
`volume_budget` is claimed: that later scalar inequality must consume this
literal sum and the enlarged common `Z0`.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

/-- Exact split of a filtered finite sum over appended `Fin` indices. -/
theorem sum_filter_fin_append
    {m n : ℕ} (p : Fin (m + n) → Prop) [DecidablePred p]
    (f : Fin (m + n) → ℝ) :
    (∑ i ∈ (Finset.univ.filter p), f i) =
      (∑ i ∈ (Finset.univ.filter fun i : Fin m =>
          p (Fin.castAdd n i)), f (Fin.castAdd n i)) +
      ∑ i ∈ (Finset.univ.filter fun i : Fin n =>
          p (Fin.natAdd m i)), f (Fin.natAdd m i) := by
  simp only [Finset.sum_filter]
  rw [Fin.sum_univ_add]

/-- The combined rooted residual ledger is exactly the direct ledger plus
the native Lemma-1 ledger. -/
theorem sum_cmp116Eq80Lemma1Combined_rootedResidual_eq
    {Index : Type*} {M Q Nc q : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (root : FinBox 4 (2 * Q))
    (E0 epsilon1 C1 C2 kappa1 delta kappa alpha4 : ℝ) :
    (∑ Y ∈ (Finset.univ.filter fun Y :
          Fin (CMP116Eq80Lemma1CombinedDomainCount anchor D E) =>
        root ∈ cmp116Eq80Lemma1CombinedDomainSupport anchor D E Y),
      cmp116Eq220CenteredSourceResidualWeight
        (fun y =>
          (cmp116Eq80Lemma1CombinedDomainMetric anchor D E y : ℝ))
        E0 epsilon1 C1 M q C2 kappa1 delta kappa alpha4 Y) =
      (∑ Y ∈ (Finset.univ.filter fun Y :
            Fin (CMP102Eq80SourcePi4DomainCount anchor D) =>
          root ∈
            (cmp102Eq80SourcePi4IndexedLocalizationDomain
              (M := M) anchor D Y).blocks),
        cmp116Eq220CenteredSourceResidualWeight
          (fun y =>
            (cmp102Eq80SourcePi4IndexedDomainMetricNat
              (M := M) anchor D y : ℝ))
          E0 epsilon1 C1 M q C2 kappa1 delta kappa alpha4 Y) +
      ∑ Y ∈ (Finset.univ.filter fun Y :
            Fin (CMP109Lemma1NativeDomainCount E) =>
          root ∈ cmp109Lemma1NativeIndexedDomainSupport E Y),
        cmp116Eq220CenteredSourceResidualWeight
          (fun y =>
            (cmp109Lemma1NativeIndexedDomainMetric E y : ℝ))
          E0 epsilon1 C1 M q C2 kappa1 delta kappa alpha4 Y := by
  rw [sum_filter_fin_append]
  simp only [cmp116Eq220CenteredSourceResidualWeight,
    cmp116Eq80Lemma1CombinedDomainSupport_direct,
    cmp116Eq80Lemma1CombinedDomainSupport_native,
    cmp116Eq80Lemma1CombinedDomainMetric_direct,
    cmp116Eq80Lemma1CombinedDomainMetric_native]

/-- Explicit common bound consumed by the terminal ledger. -/
noncomputable def cmp116Eq80Lemma1CombinedRootBound
    (directRootBound : ℝ)
    (E0 epsilon1 C1 : ℝ) (M q : ℕ)
    (C2 kappa1 delta kappa alpha4 : ℝ) : ℝ :=
  directRootBound +
    cmp109Lemma1NativeRootBound
      E0 epsilon1 C1 M q C2 kappa1 delta kappa alpha4

/-- Nonnegativity of the common bound is inherited sector by sector. -/
theorem cmp116Eq80Lemma1CombinedRootBound_nonneg
    {directRootBound E0 epsilon1 C1 C2 kappa1 delta kappa alpha4 : ℝ}
    {M q : ℕ}
    (hdirect : 0 ≤ directRootBound)
    (hE0 : 0 ≤ E0) (hepsilon1 : 0 ≤ epsilon1)
    (hC1 : 0 ≤ C1) (halpha4 : 0 ≤ alpha4)
    (hsmall1 :
      64 * Real.exp (-(((1 - 2 * delta) * kappa) / 24)) < 1)
    (hsmall2 :
      64 * Real.exp (-((delta * kappa) / 24)) < 1) :
    0 ≤ cmp116Eq80Lemma1CombinedRootBound directRootBound
      E0 epsilon1 C1 M q C2 kappa1 delta kappa alpha4 := by
  unfold cmp116Eq80Lemma1CombinedRootBound
  exact add_nonneg hdirect
    (cmp109Lemma1NativeRootBound_nonneg
      hE0 hepsilon1 hC1 halpha4 hsmall1 hsmall2)

/-- A rooted bound for the direct sector and the already constructed native
animal estimate give the exact rooted bound for every combined index.

The direct input is required for every coarse root, matching the strength of
the native theorem and avoiding a special case for the enlarged part of
`Z0`. -/
theorem cmp116Eq80Lemma1Combined_rooted_residual_le
    {Index : Type*} {M Q Nc q : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (directRootBound : ℝ)
    (E0 epsilon1 C1 C2 kappa1 delta kappa alpha4 : ℝ)
    (hdirect : ∀ root : FinBox 4 (2 * Q),
      (∑ Y ∈ (Finset.univ.filter fun Y :
            Fin (CMP102Eq80SourcePi4DomainCount anchor D) =>
          root ∈
            (cmp102Eq80SourcePi4IndexedLocalizationDomain
              (M := M) anchor D Y).blocks),
        cmp116Eq220CenteredSourceResidualWeight
          (fun y =>
            (cmp102Eq80SourcePi4IndexedDomainMetricNat
              (M := M) anchor D y : ℝ))
          E0 epsilon1 C1 M q C2 kappa1 delta kappa alpha4 Y) ≤
        directRootBound)
    (hE0 : 0 ≤ E0) (hepsilon1 : 0 ≤ epsilon1)
    (hC1 : 0 ≤ C1) (halpha4 : 0 ≤ alpha4)
    (hrate1 : 0 ≤ (1 - 2 * delta) * kappa)
    (hrate2 : 0 ≤ delta * kappa)
    (hsmall1 :
      64 * Real.exp (-(((1 - 2 * delta) * kappa) / 24)) < 1)
    (hsmall2 :
      64 * Real.exp (-((delta * kappa) / 24)) < 1)
    (root : FinBox 4 (2 * Q)) :
    (∑ Y ∈ (Finset.univ.filter fun Y :
          Fin (CMP116Eq80Lemma1CombinedDomainCount anchor D E) =>
        root ∈ cmp116Eq80Lemma1CombinedDomainSupport anchor D E Y),
      cmp116Eq220CenteredSourceResidualWeight
        (fun y =>
          (cmp116Eq80Lemma1CombinedDomainMetric anchor D E y : ℝ))
        E0 epsilon1 C1 M q C2 kappa1 delta kappa alpha4 Y) ≤
      cmp116Eq80Lemma1CombinedRootBound directRootBound
        E0 epsilon1 C1 M q C2 kappa1 delta kappa alpha4 := by
  rw [sum_cmp116Eq80Lemma1Combined_rootedResidual_eq]
  unfold cmp116Eq80Lemma1CombinedRootBound
  exact add_le_add (hdirect root)
    (cmp109Lemma1NativeIndexed_rooted_residual_le
      E root E0 epsilon1 C1 C2 kappa1 delta kappa alpha4
      hE0 hepsilon1 hC1 halpha4 hrate1 hrate2 hsmall1 hsmall2)

/-- Literal physical common bound after discharging both the direct and
native rooted ledgers. -/
noncomputable def cmp116Eq80Lemma1CombinedPhysicalRootBound
    (E0 epsilon1 C1 : ℝ) (M q : ℕ)
    (C2 kappa1 delta kappa alpha4 : ℝ) : ℝ :=
  cmp102Eq80SourcePi4DirectRootBound
      E0 epsilon1 C1 M q C2 kappa1 delta kappa alpha4 +
    cmp109Lemma1NativeRootBound
      E0 epsilon1 C1 M q C2 kappa1 delta kappa alpha4

/-- The combined physical root bound is nonnegative under exactly the two
animal windows used by its sector estimates. -/
theorem cmp116Eq80Lemma1CombinedPhysicalRootBound_nonneg
    {E0 epsilon1 C1 C2 kappa1 delta kappa alpha4 : ℝ}
    {M q : ℕ}
    (hE0 : 0 ≤ E0) (hepsilon1 : 0 ≤ epsilon1)
    (hC1 : 0 ≤ C1) (halpha4 : 0 ≤ alpha4)
    (hsmall1 :
      64 * Real.exp (-(((1 - 2 * delta) * kappa) / 24)) < 1)
    (hsmall2 :
      64 * Real.exp (-((delta * kappa) / 24)) < 1) :
    0 ≤ cmp116Eq80Lemma1CombinedPhysicalRootBound
      E0 epsilon1 C1 M q C2 kappa1 delta kappa alpha4 := by
  unfold cmp116Eq80Lemma1CombinedPhysicalRootBound
  exact add_nonneg
    (cmp102Eq80SourcePi4DirectRootBound_nonneg
      hE0 hepsilon1 hC1 halpha4 hsmall1 hsmall2)
    (cmp109Lemma1NativeRootBound_nonneg
      hE0 hepsilon1 hC1 halpha4 hsmall1 hsmall2)

/-- Both physical sector estimates discharge the exact rooted residual
ledger for the canonical combined index.  No rooted sum is a premise. -/
theorem cmp116Eq80Lemma1Combined_rooted_residual_le_physical
    {Index : Type*} {M Q Nc q : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (E0 epsilon1 C1 C2 kappa1 delta kappa alpha4 : ℝ)
    (hE0 : 0 ≤ E0) (hepsilon1 : 0 ≤ epsilon1)
    (hC1 : 0 ≤ C1) (halpha4 : 0 ≤ alpha4)
    (hrate1 : 0 ≤ (1 - 2 * delta) * kappa)
    (hrate2 : 0 ≤ delta * kappa)
    (hsmall1 :
      64 * Real.exp (-(((1 - 2 * delta) * kappa) / 24)) < 1)
    (hsmall2 :
      64 * Real.exp (-((delta * kappa) / 24)) < 1)
    (root : FinBox 4 (2 * Q)) :
    (∑ Y ∈ (Finset.univ.filter fun Y :
          Fin (CMP116Eq80Lemma1CombinedDomainCount anchor D E) =>
        root ∈ cmp116Eq80Lemma1CombinedDomainSupport anchor D E Y),
      cmp116Eq220CenteredSourceResidualWeight
        (fun y =>
          (cmp116Eq80Lemma1CombinedDomainMetric anchor D E y : ℝ))
        E0 epsilon1 C1 M q C2 kappa1 delta kappa alpha4 Y) ≤
      cmp116Eq80Lemma1CombinedPhysicalRootBound
        E0 epsilon1 C1 M q C2 kappa1 delta kappa alpha4 := by
  change _ ≤ cmp116Eq80Lemma1CombinedRootBound
    (cmp102Eq80SourcePi4DirectRootBound
      E0 epsilon1 C1 M q C2 kappa1 delta kappa alpha4)
    E0 epsilon1 C1 M q C2 kappa1 delta kappa alpha4
  exact cmp116Eq80Lemma1Combined_rooted_residual_le
    anchor D E
    (cmp102Eq80SourcePi4DirectRootBound
      E0 epsilon1 C1 M q C2 kappa1 delta kappa alpha4)
    E0 epsilon1 C1 C2 kappa1 delta kappa alpha4
    (fun r =>
      cmp102Eq80SourcePi4Indexed_rooted_residual_le
        anchor D r E0 epsilon1 C1 C2 kappa1 delta kappa alpha4
        hE0 hepsilon1 hC1 halpha4 hrate1 hrate2 hsmall1 hsmall2)
    hE0 hepsilon1 hC1 halpha4 hrate1 hrate2 hsmall1 hsmall2 root

end

end YangMills.RG
