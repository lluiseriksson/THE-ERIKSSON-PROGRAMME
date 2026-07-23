/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq226SourceLedger

/-!
# Source domain dictionary for the CMP116 equation-(2.26) product

The analytic term indexes its localization domains by `Fin nY`, whereas the
later resummation uses a finite family of physical domains.  The canonical
dictionary is the image of the literal `domainSupport` map.  If this map is
injective and the stored metric is the physical metric of its support, the
two equation-(2.26) products are exactly equal.
-/

namespace YangMills.RG

noncomputable section

/-- The physical finite domain family carried by one analytic source term. -/
def cmp116Eq226SourceDomainParts
    {nY : ℕ} {V : Type*} [DecidableEq V]
    (domainSupport : Fin nY → Finset V) : Finset (Finset V) :=
  Finset.univ.image domainSupport

theorem mem_cmp116Eq226SourceDomainParts_iff
    {nY : ℕ} {V : Type*} [DecidableEq V]
    (domainSupport : Fin nY → Finset V) (Y : Finset V) :
    Y ∈ cmp116Eq226SourceDomainParts domainSupport ↔
      ∃ i : Fin nY, domainSupport i = Y := by
  simp [cmp116Eq226SourceDomainParts]

/-- Injectivity of the source domain enumeration makes the canonical family
have exactly `nY` elements. -/
theorem card_cmp116Eq226SourceDomainParts
    {nY : ℕ} {V : Type*} [DecidableEq V]
    (domainSupport : Fin nY → Finset V)
    (hinjective : Function.Injective domainSupport) :
    (cmp116Eq226SourceDomainParts domainSupport).card = nY := by
  rw [cmp116Eq226SourceDomainParts, Finset.card_image_iff.mpr]
  · simp
  · intro i _ j _ hij
    exact hinjective hij

/-- Exact equality between the `Fin nY` source product and the product over
the physical image family. -/
theorem cmp116Eq226DomainProduct_eq_sourceDomainParts
    {nY : ℕ} {V : Type*} [DecidableEq V]
    (E0 epsilon1 C1 alpha4 : ℝ) (M q : ℕ)
    (C2 kappa1 delta kappa : ℝ)
    (domainSupport : Fin nY → Finset V)
    (domainMetric : Fin nY → ℕ)
    (physicalMetric : Finset V → ℕ)
    (hinjective : Function.Injective domainSupport)
    (hmetric :
      ∀ i, domainMetric i = physicalMetric (domainSupport i)) :
    cmp116Eq226DomainProduct
        E0 epsilon1 C1 alpha4 M q C2 kappa1 delta kappa
        domainMetric Finset.univ =
      cmp116Eq226DomainProduct
        E0 epsilon1 C1 alpha4 M q C2 kappa1 delta kappa
        physicalMetric (cmp116Eq226SourceDomainParts domainSupport) := by
  unfold cmp116Eq226DomainProduct cmp116Eq226SourceDomainParts
  rw [Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro i _hi
    unfold cmp116Eq226DomainFactor
    rw [hmetric i]
  · intro i _hi j _hj hij
    exact hinjective hij

/-- Reindexing by an externally named physical family, provided it is
literally the canonical image of the source supports. -/
theorem cmp116Eq226DomainProduct_eq_of_sourceDomainDictionary
    {nY : ℕ} {V : Type*} [DecidableEq V]
    (E0 epsilon1 C1 alpha4 : ℝ) (M q : ℕ)
    (C2 kappa1 delta kappa : ℝ)
    (domainSupport : Fin nY → Finset V)
    (domainMetric : Fin nY → ℕ)
    (physicalMetric : Finset V → ℕ)
    (DParts : Finset (Finset V))
    (hinjective : Function.Injective domainSupport)
    (hmetric :
      ∀ i, domainMetric i = physicalMetric (domainSupport i))
    (hparts :
      DParts = cmp116Eq226SourceDomainParts domainSupport) :
    cmp116Eq226DomainProduct
        E0 epsilon1 C1 alpha4 M q C2 kappa1 delta kappa
        domainMetric Finset.univ =
      cmp116Eq226DomainProduct
        E0 epsilon1 C1 alpha4 M q C2 kappa1 delta kappa
        physicalMetric DParts := by
  subst DParts
  exact
    cmp116Eq226DomainProduct_eq_sourceDomainParts
      E0 epsilon1 C1 alpha4 M q C2 kappa1 delta kappa
      domainSupport domainMetric physicalMetric hinjective hmetric

end

end YangMills.RG
