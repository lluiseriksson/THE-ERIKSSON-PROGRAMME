/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq80Lemma1CombinedDomainDictionary
import YangMills.RG.BalabanCMP116Eq219SourceGeometry

/-!
# Literal kernel support on the direct/native CMP116 ledger

**VALIDATED INTERMEDIATE BRICK.** This source and its public audit were
materialized from source checkpoint `134a21f0` in one fresh Colab Pro+ clone;
the focal queue, `YangMillsCore`, and the full oracle all exited zero.  The
evidence archive has SHA-256 `589769BC64D24493B0F68F5B0458DB017258919B32C265D8C83FA327487233EC`.

For a direct equation-(80) domain, the fixed quadratic core is projected in
both arguments onto the physical bilateral bond support of that domain.  Its
literal kernel support therefore requires both bonds to lie in that support.

For a native CMP109 Lemma-1 index the fixed quadratic core is identically
zero: the same residual is present in `total` and `residual`.  Its kernel
support is consequently empty.  This is not a zero extension of the native
activity; only the quadratic core used by equation (1.43) vanishes.

The metric budget is derived from the physical source geometry.  The domain
cardinality used here is already the normalized count `M⁻⁴ |Y|`, represented
by `CMP116LocalizationDomain.blocks.card`; no second factor `M⁻⁴` occurs.
-/

namespace YangMills.RG

noncomputable section

/-- Literal support of the fixed Hessian kernel on the appended ledger. -/
noncomputable def cmp116Eq80Lemma1CombinedKernelSupport
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc) :
    Fin (CMP116Eq80Lemma1CombinedDomainCount anchor D E) →
      PhysicalBond 4 (M * (2 * Q)) →
      PhysicalBond 4 (M * (2 * Q)) → Prop :=
  Fin.addCases
    (fun i source target =>
      source ∈ (cmp102Eq80SourcePi4IndexedLocalizationDomain
          (M := M) anchor D i).bondSupport ∧
        target ∈ (cmp102Eq80SourcePi4IndexedLocalizationDomain
          (M := M) anchor D i).bondSupport)
    (fun _ _ _ => False)

@[simp] theorem cmp116Eq80Lemma1CombinedKernelSupport_direct
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (i : Fin (CMP102Eq80SourcePi4DomainCount anchor D))
    (source target : PhysicalBond 4 (M * (2 * Q))) :
    cmp116Eq80Lemma1CombinedKernelSupport anchor D E
        (Fin.castAdd (CMP109Lemma1NativeDomainCount E) i) source target ↔
      source ∈ (cmp102Eq80SourcePi4IndexedLocalizationDomain
          (M := M) anchor D i).bondSupport ∧
        target ∈ (cmp102Eq80SourcePi4IndexedLocalizationDomain
          (M := M) anchor D i).bondSupport := by
  simp [cmp116Eq80Lemma1CombinedKernelSupport]

@[simp] theorem cmp116Eq80Lemma1CombinedKernelSupport_native
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (i : Fin (CMP109Lemma1NativeDomainCount E))
    (source target : PhysicalBond 4 (M * (2 * Q))) :
    ¬ cmp116Eq80Lemma1CombinedKernelSupport anchor D E
      (Fin.natAdd (CMP102Eq80SourcePi4DomainCount anchor D) i)
      source target := by
  simp [cmp116Eq80Lemma1CombinedKernelSupport]

/-- The terminal equation-(2.19) metric budget follows on every combined
index from the literal support.  Direct indices use the source-domain
diameter theorem; native indices are impossible because their support is
empty. -/
theorem cmp116Eq80Lemma1CombinedKernelSupport_metricBudget
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    {kappa1 : ℝ} (hkappa1 : 1 ≤ kappa1) :
    ∀ y source target,
      cmp116Eq80Lemma1CombinedKernelSupport anchor D E y source target →
        cmp116Eq219InternalRate M kappa1 *
            (physicalBondDist target source : ℝ) ≤
          (1 / 4 : ℝ) * (kappa1 - 1) *
            cmp116Eq80Lemma1CombinedDomainCard anchor D E y := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_)
  · intro source target hsupp
    have hsupp' :
        source ∈ (cmp102Eq80SourcePi4IndexedLocalizationDomain
            (M := M) anchor D i).bondSupport ∧
          target ∈ (cmp102Eq80SourcePi4IndexedLocalizationDomain
            (M := M) anchor D i).bondSupport := by
      simpa using hsupp
    simpa [cmp102Eq80SourcePi4IndexedDomainCard] using
      (cmp116Eq219_sourceGeometry_normalizedCard
        (cmp102Eq80SourcePi4IndexedLocalizationDomain
          (M := M) anchor D i)
        hsupp'.2 hsupp'.1 hkappa1)
  · intro source target hsupp
    exact (cmp116Eq80Lemma1CombinedKernelSupport_native
      anchor D E i source target hsupp).elim

end

end YangMills.RG
