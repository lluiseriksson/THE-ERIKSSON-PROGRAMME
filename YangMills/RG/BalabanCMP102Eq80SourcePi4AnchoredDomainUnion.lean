/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4CarrierAnchoredLocalization
import YangMills.RG.ClusterDecay

/-!
# Finite unions of equation-(80) source domains sharing `Pi^4`

Higher mixed derivatives of the literal equation-(80) potential contain
products and multilinear expressions involving several differentiated
propagators.  Their source label is the union of the source labels of every
differentiated factor.  Each such label contains the same literal `Pi^4`
carrier.

This file proves the finite geometric fact needed by that construction:
adjoining any finite family of connected domains containing a common,
nonempty connected anchor produces a connected union.  It then specializes
the result to the physical `Pi^4` carrier.  No analytic coefficient or
activity is introduced here.
-/

namespace YangMills.RG

noncomputable section

/-- A common connected anchor keeps a finite union of connected domains
connected.  The anchor is included explicitly, so the statement also covers
the empty family without a separate nonemptiness condition on the index
finset. -/
theorem walkConnected_anchor_union_biUnion
    {V ι : Type*} [DecidableEq V] [DecidableEq ι]
    (G : SimpleGraph V)
    (anchor : Finset V)
    (I : Finset ι)
    (domain : ι → Finset V)
    (hanchorNonempty : anchor.Nonempty)
    (hanchorConnected : walkConnected G anchor)
    (hsubset : ∀ i ∈ I, anchor ⊆ domain i)
    (hconnected : ∀ i ∈ I, walkConnected G (domain i)) :
    walkConnected G (anchor ∪ I.biUnion domain) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
      simpa using hanchorConnected
  | @insert i I hi ih =>
      have htailSubset : ∀ j ∈ I, anchor ⊆ domain j := by
        intro j hj
        exact hsubset j (Finset.mem_insert_of_mem hj)
      have htailConnected :
          ∀ j ∈ I, walkConnected G (domain j) := by
        intro j hj
        exact hconnected j (Finset.mem_insert_of_mem hj)
      have htail :
          walkConnected G (anchor ∪ I.biUnion domain) :=
        ih htailSubset htailConnected
      have hiConnected : walkConnected G (domain i) :=
        hconnected i (Finset.mem_insert_self i I)
      have hinter :
          ¬ Disjoint (anchor ∪ I.biUnion domain) (domain i) := by
        rw [Finset.not_disjoint_iff]
        obtain ⟨x, hx⟩ := hanchorNonempty
        exact ⟨x, Finset.mem_union_left _ hx,
          hsubset i (Finset.mem_insert_self i I) hx⟩
      simpa [Finset.biUnion_insert, Finset.union_assoc,
        Finset.union_comm, Finset.union_left_comm] using
        walkConnected_union G (anchor ∪ I.biUnion domain) (domain i)
          htail hiConnected (Or.inl hinter)

/-- Canonical source label of a finite family of equation-(80) factors:
the literal `Pi^4` carrier together with all factor domains. -/
noncomputable def cmp102Eq80SourcePi4AnchoredDomainUnion
    {Q ι : ℕ} [NeZero Q]
    (anchor : FinBox 4 Q)
    (I : Finset (Fin ι))
    (domain : Fin ι → Finset (FinBox 4 (2 * Q))) :
    Finset (FinBox 4 (2 * Q)) :=
  cmp102Eq80SourcePi4AnchorCarrier anchor ∪ I.biUnion domain

/-- The literal `Pi^4` carrier is retained by every finite source union. -/
theorem cmp102Eq80SourcePi4AnchorCarrier_subset_anchoredDomainUnion
    {Q ι : ℕ} [NeZero Q]
    (anchor : FinBox 4 Q)
    (I : Finset (Fin ι))
    (domain : Fin ι → Finset (FinBox 4 (2 * Q))) :
    cmp102Eq80SourcePi4AnchorCarrier anchor ⊆
      cmp102Eq80SourcePi4AnchoredDomainUnion anchor I domain := by
  intro x hx
  exact Finset.mem_union_left _ hx

/-- Every selected factor domain is retained by the finite source union. -/
theorem subset_cmp102Eq80SourcePi4AnchoredDomainUnion
    {Q ι : ℕ} [NeZero Q]
    (anchor : FinBox 4 Q)
    (I : Finset (Fin ι))
    (domain : Fin ι → Finset (FinBox 4 (2 * Q)))
    (i : Fin ι) (hi : i ∈ I) :
    domain i ⊆
      cmp102Eq80SourcePi4AnchoredDomainUnion anchor I domain := by
  intro x hx
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨i, hi, hx⟩

/-- A finite union of physical source domains is face-connected whenever
each factor domain is face-connected and contains the full literal `Pi^4`
carrier. -/
theorem walkConnected_cmp102Eq80SourcePi4AnchoredDomainUnion
    {Q ι : ℕ} [NeZero Q]
    (anchor : FinBox 4 Q)
    (I : Finset (Fin ι))
    (domain : Fin ι → Finset (FinBox 4 (2 * Q)))
    (hsubset : ∀ i ∈ I,
      cmp102Eq80SourcePi4AnchorCarrier anchor ⊆ domain i)
    (hconnected : ∀ i ∈ I,
      walkConnected (cmp116CoarseFaceAdj 4 (2 * Q)) (domain i)) :
    walkConnected (cmp116CoarseFaceAdj 4 (2 * Q))
      (cmp102Eq80SourcePi4AnchoredDomainUnion anchor I domain) := by
  exact walkConnected_anchor_union_biUnion
    (cmp116CoarseFaceAdj 4 (2 * Q))
    (cmp102Eq80SourcePi4AnchorCarrier anchor)
    I domain
    (cmp102Eq80SourcePi4AnchorCarrier_nonempty anchor)
    (walkConnected_cmp102Eq80SourcePi4AnchorCarrier anchor)
    hsubset hconnected

/-- Source label of a pair of differentiated factors.  The common anchor is
kept explicitly; this makes the definition total even on algebraically zero
or unsupported factor labels. -/
noncomputable def cmp102Eq80SourcePi4AnchoredPairDomain
    {Q : ℕ} [NeZero Q]
    (anchor : FinBox 4 Q)
    (YZ : Finset (FinBox 4 (2 * Q)) ×
      Finset (FinBox 4 (2 * Q))) :
    Finset (FinBox 4 (2 * Q)) :=
  cmp102Eq80SourcePi4AnchorCarrier anchor ∪ YZ.1 ∪ YZ.2

/-- The common `Pi^4` carrier is retained by a paired source label. -/
theorem cmp102Eq80SourcePi4AnchorCarrier_subset_anchoredPairDomain
    {Q : ℕ} [NeZero Q]
    (anchor : FinBox 4 Q)
    (YZ : Finset (FinBox 4 (2 * Q)) ×
      Finset (FinBox 4 (2 * Q))) :
    cmp102Eq80SourcePi4AnchorCarrier anchor ⊆
      cmp102Eq80SourcePi4AnchoredPairDomain anchor YZ := by
  intro x hx
  exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)

/-- Both factor domains are retained by their paired source label. -/
theorem pair_subset_cmp102Eq80SourcePi4AnchoredPairDomain
    {Q : ℕ} [NeZero Q]
    (anchor : FinBox 4 Q)
    (YZ : Finset (FinBox 4 (2 * Q)) ×
      Finset (FinBox 4 (2 * Q))) :
    YZ.1 ⊆ cmp102Eq80SourcePi4AnchoredPairDomain anchor YZ ∧
      YZ.2 ⊆ cmp102Eq80SourcePi4AnchoredPairDomain anchor YZ := by
  constructor
  · intro x hx
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  · intro x hx
    exact Finset.mem_union_right _ hx

/-- The union label of two connected physical factor domains remains
connected when both factors contain the same literal `Pi^4` carrier. -/
theorem walkConnected_cmp102Eq80SourcePi4AnchoredPairDomain
    {Q : ℕ} [NeZero Q]
    (anchor : FinBox 4 Q)
    (YZ : Finset (FinBox 4 (2 * Q)) ×
      Finset (FinBox 4 (2 * Q)))
    (hsubset₁ :
      cmp102Eq80SourcePi4AnchorCarrier anchor ⊆ YZ.1)
    (hsubset₂ :
      cmp102Eq80SourcePi4AnchorCarrier anchor ⊆ YZ.2)
    (hconnected₁ :
      walkConnected (cmp116CoarseFaceAdj 4 (2 * Q)) YZ.1)
    (hconnected₂ :
      walkConnected (cmp116CoarseFaceAdj 4 (2 * Q)) YZ.2) :
    walkConnected (cmp116CoarseFaceAdj 4 (2 * Q))
      (cmp102Eq80SourcePi4AnchoredPairDomain anchor YZ) := by
  classical
  let G := cmp116CoarseFaceAdj 4 (2 * Q)
  have hinter₁ :
      ¬ Disjoint (cmp102Eq80SourcePi4AnchorCarrier anchor) YZ.1 := by
    rw [Finset.not_disjoint_iff]
    obtain ⟨x, hx⟩ :=
      cmp102Eq80SourcePi4AnchorCarrier_nonempty anchor
    exact ⟨x, hx, hsubset₁ hx⟩
  have hfirst :
      walkConnected G
        (cmp102Eq80SourcePi4AnchorCarrier anchor ∪ YZ.1) :=
    walkConnected_union G
      (cmp102Eq80SourcePi4AnchorCarrier anchor) YZ.1
      (walkConnected_cmp102Eq80SourcePi4AnchorCarrier anchor)
      hconnected₁ (Or.inl hinter₁)
  have hinter₂ :
      ¬ Disjoint
        (cmp102Eq80SourcePi4AnchorCarrier anchor ∪ YZ.1) YZ.2 := by
    rw [Finset.not_disjoint_iff]
    obtain ⟨x, hx⟩ :=
      cmp102Eq80SourcePi4AnchorCarrier_nonempty anchor
    exact ⟨x, Finset.mem_union_left _ hx, hsubset₂ hx⟩
  exact walkConnected_union G
    (cmp102Eq80SourcePi4AnchorCarrier anchor ∪ YZ.1) YZ.2
    hfirst hconnected₂ (Or.inl hinter₂)

/-- Exact finite fiber of paired terms whose physical source label is `W`.
-/
noncomputable def cmp102Eq80SourcePi4AnchoredPairFiber
    {Q : ℕ} [NeZero Q] {E : Type*} [AddCommMonoid E]
    (anchor : FinBox 4 Q)
    (term : (Finset (FinBox 4 (2 * Q)) ×
      Finset (FinBox 4 (2 * Q))) → E)
    (W : Finset (FinBox 4 (2 * Q))) : E :=
  ∑ YZ ∈ (Finset.univ :
      Finset (Finset (FinBox 4 (2 * Q)) ×
        Finset (FinBox 4 (2 * Q)))).filter
        (fun YZ =>
          cmp102Eq80SourcePi4AnchoredPairDomain anchor YZ = W),
    term YZ

/-- Exact regrouping of every paired term by the union of the two factor
domains and the common physical `Pi^4` carrier. -/
theorem sum_cmp102Eq80SourcePi4AnchoredPairFiber
    {Q : ℕ} [NeZero Q] {E : Type*} [AddCommMonoid E]
    (anchor : FinBox 4 Q)
    (term : (Finset (FinBox 4 (2 * Q)) ×
      Finset (FinBox 4 (2 * Q))) → E) :
    (∑ YZ : Finset (FinBox 4 (2 * Q)) ×
        Finset (FinBox 4 (2 * Q)), term YZ) =
      ∑ W : Finset (FinBox 4 (2 * Q)),
        cmp102Eq80SourcePi4AnchoredPairFiber anchor term W := by
  classical
  unfold cmp102Eq80SourcePi4AnchoredPairFiber
  exact (Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ :
      Finset (Finset (FinBox 4 (2 * Q)) ×
        Finset (FinBox 4 (2 * Q)))))
    (t := (Finset.univ :
      Finset (Finset (FinBox 4 (2 * Q)))))
    (g := cmp102Eq80SourcePi4AnchoredPairDomain anchor)
    (f := term)
    (fun _ _ => Finset.mem_univ _)).symm

end

end YangMills.RG
