/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq219SourceGeometry
import YangMills.RG.LocalFunctional

/-!
# The localized-action side of the CMP109 energy difference

The second expression in CMP109 equation (2.12) is a difference of the
inductive effective action evaluated at two physical gauge backgrounds.  It is
one source sector of the later CMP116 residual `V''_k`; it is not part of the
quadratic `Q_Y` branch governed by equation (1.43).

This file introduces only the source structure that is already present in the
inductive hypothesis: on a finite periodic volume, the effective action is a
finite sum of functionals carrying an RG-scale label and a nonempty
face-connected localization domain.  Each summand is type-local on physical
bonds and its support is contained in the literal bilateral bond support of
its domain.  The term index is deliberately not identified with the domain:
distinct scales or source species may have the same geometric carrier.

The main theorem proves exact cancellation of every summand whose support does
not meet the bonds changed between the two backgrounds.  Thus the CMP109
energy difference is reduced to the domains that actually see the
perturbation.  No residual `V''_k`, equation-(1.36) estimate, or decay
majorant is assumed here.

Honest scope: this is the finite-volume localized expansion consumed by the
CMP109 Lemma-1 sector, not a construction of the RG induction itself.  The
source producer must still instantiate the summands from the previous-scale
effective action and prove their analytic decay.  The concrete maps
`U_k(exp(i[g_k C B - h D_tilde(g_k C B)]) V^(k))` and `U_k(V^(k))` are also
still to be installed as the two backgrounds.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No placeholders or
local axioms.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

/-- Finite-volume localized expansion of the CMP109 effective-action input.
Every term retains its RG-scale label and a literal nonempty face-connected
coarse-block domain, and its local support is contained in the physical bonds
of that domain. -/
structure CMP109LocalizedActionExpansion
    (Index : Type*) (M N' Nc : ℕ) [NeZero M] [NeZero N'] where
  terms : Finset Index
  /-- RG scale label `j` of the localized contribution `E^(j)(X)`. -/
  scale : Index → ℕ
  /-- The source localization domain, transported to the current physical
  bond lattice.  Keeping it separate from the term index allows distinct
  scales or source species to share the same geometric carrier. -/
  domainOf : Index → CMP116LocalizationDomain M N'
  activity :
    Index →
      LocalFunctional
        (PhysicalBond 4 (M * N'))
        (fun _ => SUN Nc) ℝ
  support_subset_domain :
    ∀ i ∈ terms, (activity i).support ⊆ (domainOf i).bondSupport

namespace CMP109LocalizedActionExpansion

variable {Index : Type*} {M N' Nc : ℕ} [NeZero M] [NeZero N']

/-- Restriction of a full oriented gauge configuration to its positive
physical bonds.  The inverse-orientation values remain determined by the
`GaugeConfig` law and are not independent local coordinates. -/
def positiveBondField
    (U : PhysicalGaugeBackground 4 (M * N') Nc) :
    PhysicalBond 4 (M * N') → SUN Nc :=
  fun b => U (ConcreteEdge.mk b.1 b.2 true)

/-- The canonical finite set of positive physical bonds on which two
backgrounds differ.  This removes any auxiliary choice of a perturbation
carrier from the exact localization theorem. -/
noncomputable def changedPositiveBonds
    (perturbed base : PhysicalGaugeBackground 4 (M * N') Nc) :
    Finset (PhysicalBond 4 (M * N')) :=
  Finset.univ.filter fun b =>
    positiveBondField perturbed b ≠ positiveBondField base b

/-- Outside the canonical changed-bond set, the restricted physical
backgrounds agree by construction. -/
theorem positiveBondField_eq_of_not_mem_changedPositiveBonds
    (perturbed base : PhysicalGaugeBackground 4 (M * N') Nc)
    {b : PhysicalBond 4 (M * N')}
    (hb : b ∉ changedPositiveBonds perturbed base) :
    positiveBondField perturbed b = positiveBondField base b := by
  classical
  simpa [changedPositiveBonds] using hb

/-- Evaluation of the localized effective action on a physical gauge
background. -/
noncomputable def globalEval
    (E : CMP109LocalizedActionExpansion Index M N' Nc)
    (U : PhysicalGaugeBackground 4 (M * N') Nc) : ℝ :=
  ∑ i ∈ E.terms, (E.activity i).globalEval (positiveBondField U)

/-- The literal CMP109 energy difference before the source-specific
background maps are substituted. -/
noncomputable def energyDifference
    (E : CMP109LocalizedActionExpansion Index M N' Nc)
    (perturbed base : PhysicalGaugeBackground 4 (M * N') Nc) : ℝ :=
  E.globalEval perturbed - E.globalEval base

/-- Domains whose actual local-functional support meets the bonds changed by
the physical perturbation. -/
noncomputable def affectedDomains
    (E : CMP109LocalizedActionExpansion Index M N' Nc)
    (changed : Finset (PhysicalBond 4 (M * N'))) :
    Finset Index :=
  E.terms.filter fun i => ¬ Disjoint (E.activity i).support changed

/-- If two backgrounds agree off `changed`, a local summand disjoint from
`changed` evaluates identically on them. -/
theorem activity_globalEval_eq_of_disjoint_changed
    (E : CMP109LocalizedActionExpansion Index M N' Nc)
    {changed : Finset (PhysicalBond 4 (M * N'))}
    {perturbed base : PhysicalGaugeBackground 4 (M * N') Nc}
    (houtside : ∀ b, b ∉ changed →
      positiveBondField perturbed b = positiveBondField base b)
    {i : Index}
    (hdisjoint : Disjoint (E.activity i).support changed) :
    (E.activity i).globalEval (positiveBondField perturbed) =
      (E.activity i).globalEval (positiveBondField base) := by
  apply LocalFunctional.globalEval_eq_of_agreeOn
  intro b hb
  apply houtside b
  intro hbChanged
  exact Finset.disjoint_left.mp hdisjoint hb hbChanged

/-- Exact localization of the CMP109 energy difference: all domains whose
local support misses the changed bonds cancel term by term. -/
theorem energyDifference_eq_sum_affectedDomains
    (E : CMP109LocalizedActionExpansion Index M N' Nc)
    {changed : Finset (PhysicalBond 4 (M * N'))}
    {perturbed base : PhysicalGaugeBackground 4 (M * N') Nc}
    (houtside : ∀ b, b ∉ changed →
      positiveBondField perturbed b = positiveBondField base b) :
    E.energyDifference perturbed base =
      ∑ i ∈ E.affectedDomains changed,
        ((E.activity i).globalEval (positiveBondField perturbed) -
          (E.activity i).globalEval (positiveBondField base)) := by
  classical
  unfold energyDifference globalEval affectedDomains
  rw [← Finset.sum_sub_distrib]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i hi hinot
  have hdisjoint : Disjoint (E.activity i).support changed := by
    by_contra hnot
    exact hinot (Finset.mem_filter.mpr ⟨hi, hnot⟩)
  rw [activity_globalEval_eq_of_disjoint_changed E houtside hdisjoint]
  simp

/-- Triangle-inequality consequence of the exact affected-domain identity.
This is not yet equation (1.36): the source decay of the individual summands
and the uniform rooted-domain resummation remain separate analytic steps. -/
theorem norm_energyDifference_le_sum_affectedDomains
    (E : CMP109LocalizedActionExpansion Index M N' Nc)
    {changed : Finset (PhysicalBond 4 (M * N'))}
    {perturbed base : PhysicalGaugeBackground 4 (M * N') Nc}
    (houtside : ∀ b, b ∉ changed →
      positiveBondField perturbed b = positiveBondField base b) :
    ‖E.energyDifference perturbed base‖ ≤
      ∑ i ∈ E.affectedDomains changed,
        ‖(E.activity i).globalEval (positiveBondField perturbed) -
          (E.activity i).globalEval (positiveBondField base)‖ := by
  rw [energyDifference_eq_sum_affectedDomains E houtside]
  exact norm_sum_le _ _

/-- Choice-free exact localization using the literal set of positive bonds
where the two physical backgrounds differ. -/
theorem energyDifference_eq_sum_changedPositiveBonds
    (E : CMP109LocalizedActionExpansion Index M N' Nc)
    (perturbed base : PhysicalGaugeBackground 4 (M * N') Nc) :
    E.energyDifference perturbed base =
      ∑ i ∈ E.affectedDomains (changedPositiveBonds perturbed base),
        ((E.activity i).globalEval (positiveBondField perturbed) -
          (E.activity i).globalEval (positiveBondField base)) := by
  apply E.energyDifference_eq_sum_affectedDomains
  intro b hb
  exact positiveBondField_eq_of_not_mem_changedPositiveBonds perturbed base hb

/-- Choice-free triangle-inequality bound over exactly those localized terms
whose support sees a changed positive bond.  The termwise analytic decay
needed for equation (1.36) is deliberately not assumed here. -/
theorem norm_energyDifference_le_sum_changedPositiveBonds
    (E : CMP109LocalizedActionExpansion Index M N' Nc)
    (perturbed base : PhysicalGaugeBackground 4 (M * N') Nc) :
    ‖E.energyDifference perturbed base‖ ≤
      ∑ i ∈ E.affectedDomains (changedPositiveBonds perturbed base),
        ‖(E.activity i).globalEval (positiveBondField perturbed) -
          (E.activity i).globalEval (positiveBondField base)‖ := by
  apply E.norm_energyDifference_le_sum_affectedDomains
  intro b hb
  exact positiveBondField_eq_of_not_mem_changedPositiveBonds perturbed base hb

/-- Every affected domain contains a changed physical bond in its literal
bilateral domain support.  This is the geometric bridge needed before the
source decay of the inductive activities can be resummed over rooted
domains. -/
theorem affectedDomain_has_changed_bond
    (E : CMP109LocalizedActionExpansion Index M N' Nc)
    {changed : Finset (PhysicalBond 4 (M * N'))}
    {i : Index}
    (hi : i ∈ E.affectedDomains changed) :
    ∃ b, b ∈ (E.domainOf i).bondSupport ∧ b ∈ changed := by
  classical
  have hiTerm : i ∈ E.terms :=
    (Finset.mem_filter.mp hi).1
  have hnotDisjoint :
      ¬ Disjoint (E.activity i).support changed :=
    (Finset.mem_filter.mp hi).2
  rw [Finset.not_disjoint_iff] at hnotDisjoint
  obtain ⟨b, hbSupport, hbChanged⟩ := hnotDisjoint
  exact ⟨b, E.support_subset_domain i hiTerm hbSupport, hbChanged⟩

end CMP109LocalizedActionExpansion

end

end YangMills.RG
