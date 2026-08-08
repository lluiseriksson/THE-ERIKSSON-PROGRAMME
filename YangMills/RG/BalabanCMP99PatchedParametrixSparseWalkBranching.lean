/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99PatchedParametrixSparseWalk
import YangMills.RG.BalabanCMP99SimpleLocalizationDomains

/-!
# Uniform branching for sparse CMP99 patched walks

This file connects the exact physical successor relation of the patched
parametrix with the existing source-simple-domain animal count.  A source
chart dictionary must prove two transparent geometric facts: distinct charts
have distinct simple domains, and every physically near-range successor maps
to a simple domain meeting the current one.  From precisely these facts the
volume-uniform branching constant and the `K^n` tail count follow.

No cardinal bound on the ambient chart family is used.  Constructing the
concrete source chart dictionary remains the downstream geometric obligation.
-/

namespace YangMills.RG

noncomputable section

universe u

/-- The unique continuation label turns the physical chart successor family
into the generalized-walk step type used by the countable CMP99 series. -/
noncomputable def cmp99PhysicalPatchSuccessorSteps
    {ι : Type*} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (R : ℕ)
    (left : ↥charts) :
    Finset (CMP99WalkStep Unit ↥charts) :=
  (cmp99PhysicalPatchSuccessors charts core enlarged dist R left).image
    fun right => ⟨(), right⟩

@[simp]
theorem mem_cmp99PhysicalPatchSuccessorSteps_iff
    {ι : Type*} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (R : ℕ)
    (left : ↥charts) (step : CMP99WalkStep Unit ↥charts) :
    step ∈ cmp99PhysicalPatchSuccessorSteps
        charts core enlarged dist R left ↔
      CMP99PhysicalPatchCanFollow core enlarged dist R left step.domain := by
  constructor
  · intro hstep
    simp only [cmp99PhysicalPatchSuccessorSteps, Finset.mem_image] at hstep
    obtain ⟨right, hright, hEq⟩ := hstep
    cases step
    cases hEq
    exact (mem_cmp99PhysicalPatchSuccessors_iff
      charts core enlarged dist R left right).mp hright
  · intro hnear
    rw [cmp99PhysicalPatchSuccessorSteps, Finset.mem_image]
    refine ⟨step.domain, ?_, ?_⟩
    · exact (mem_cmp99PhysicalPatchSuccessors_iff
        charts core enlarged dist R left step.domain).mpr hnear
    · cases step with
      | mk label domain =>
          cases label
          rfl

/-- Adding the unique label does not change the number of physical
successors. -/
theorem card_cmp99PhysicalPatchSuccessorSteps
    {ι : Type*} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (R : ℕ)
    (left : ↥charts) :
    (cmp99PhysicalPatchSuccessorSteps
        charts core enlarged dist R left).card =
      (cmp99PhysicalPatchSuccessors charts core enlarged dist R left).card := by
  rw [cmp99PhysicalPatchSuccessorSteps, Finset.card_image_of_injective]
  intro a b hab
  exact congrArg CMP99WalkStep.domain hab

section SimpleDomainDictionary

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A source-faithful injective chart-to-simple-domain dictionary turns every
physical successor into a member of the already counted meeting-domain
family. -/
theorem image_cmp99PhysicalPatchSuccessors_subset_meetingSimpleDomains
    {ι : Type*} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (R S : ℕ)
    (domainOf : ↥charts → CMP99SimpleLocalizationDomain G S)
    (hnear : ∀ (left right : ↥charts),
      CMP99PhysicalPatchCanFollow core enlarged dist R left right →
        (domainOf left).Meets (domainOf right))
    (left : ↥charts) :
    (cmp99PhysicalPatchSuccessors charts core enlarged dist R left).image
        domainOf ⊆
      cmp99MeetingSimpleDomains G S (domainOf left) := by
  intro domain hdomain
  simp only [Finset.mem_image] at hdomain
  obtain ⟨right, hright, rfl⟩ := hdomain
  rw [cmp99MeetingSimpleDomains, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hnear left right
    ((mem_cmp99PhysicalPatchSuccessors_iff
      charts core enlarged dist R left right).mp hright)⟩

/-- Explicit volume-uniform bound for the physically surviving successor
charts.  The ambient number of charts does not occur. -/
theorem card_cmp99PhysicalPatchSuccessors_le_simpleDomainBound
    {ι : Type*} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (R S Δ : ℕ)
    (hΔ : ∀ x, G.degree x ≤ Δ) (hΔ1 : 1 ≤ Δ)
    (domainOf : ↥charts → CMP99SimpleLocalizationDomain G S)
    (hinj : Function.Injective domainOf)
    (hnear : ∀ (left right : ↥charts),
      CMP99PhysicalPatchCanFollow core enlarged dist R left right →
        (domainOf left).Meets (domainOf right))
    (left : ↥charts) :
    (cmp99PhysicalPatchSuccessors charts core enlarged dist R left).card ≤
      S * (S + 1) * Δ ^ (2 * S) := by
  calc
    (cmp99PhysicalPatchSuccessors charts core enlarged dist R left).card =
        ((cmp99PhysicalPatchSuccessors charts core enlarged dist R left).image
          domainOf).card := by
      symm
      exact Finset.card_image_of_injective _ hinj
    _ ≤ (cmp99MeetingSimpleDomains G S (domainOf left)).card :=
      Finset.card_le_card
        (image_cmp99PhysicalPatchSuccessors_subset_meetingSimpleDomains
          G charts core enlarged dist R S domainOf hnear left)
    _ ≤ S * (S + 1) * Δ ^ (2 * S) :=
      card_cmp99MeetingSimpleDomains_le G S Δ hΔ hΔ1 (domainOf left)

/-- The same explicit bound for the labelled physical successor steps. -/
theorem card_cmp99PhysicalPatchSuccessorSteps_le_simpleDomainBound
    {ι : Type*} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (R S Δ : ℕ)
    (hΔ : ∀ x, G.degree x ≤ Δ) (hΔ1 : 1 ≤ Δ)
    (domainOf : ↥charts → CMP99SimpleLocalizationDomain G S)
    (hinj : Function.Injective domainOf)
    (hnear : ∀ (left right : ↥charts),
      CMP99PhysicalPatchCanFollow core enlarged dist R left right →
        (domainOf left).Meets (domainOf right))
    (left : ↥charts) :
    (cmp99PhysicalPatchSuccessorSteps
        charts core enlarged dist R left).card ≤
      S * (S + 1) * Δ ^ (2 * S) := by
  rw [card_cmp99PhysicalPatchSuccessorSteps]
  exact card_cmp99PhysicalPatchSuccessors_le_simpleDomainBound
    G charts core enlarged dist R S Δ hΔ hΔ1 domainOf hinj hnear left

/-- Every tail generated by the physical successor family satisfies the
literal near-range chain relation. -/
theorem chain_of_mem_cmp99PhysicalPatchAdmissibleTails
    {ι : Type*} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (R : ℕ) :
    ∀ {n left tail},
      tail ∈ cmp99AdmissibleTails
        (cmp99PhysicalPatchSuccessorSteps charts core enlarged dist R)
        left n →
      (left :: tail.map CMP99WalkStep.domain).IsChain
        (fun (a b : ↥charts) =>
          CMP99PhysicalPatchCanFollow core enlarged dist R a b) := by
  exact chain_of_mem_cmp99AdmissibleTails
    (cmp99PhysicalPatchSuccessorSteps charts core enlarged dist R)
    (fun a b => CMP99PhysicalPatchCanFollow core enlarged dist R a b)
    (fun left step hstep =>
      (mem_cmp99PhysicalPatchSuccessorSteps_iff
        charts core enlarged dist R left step).mp hstep)

/-- The physically generated length-`n` tails obey the source-simple-domain
branching bound. -/
theorem card_cmp99PhysicalPatchAdmissibleTails_le_pow_simpleDomainBound
    {ι : Type*} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (R S Δ : ℕ)
    (hΔ : ∀ x, G.degree x ≤ Δ) (hΔ1 : 1 ≤ Δ)
    (domainOf : ↥charts → CMP99SimpleLocalizationDomain G S)
    (hinj : Function.Injective domainOf)
    (hnear : ∀ (left right : ↥charts),
      CMP99PhysicalPatchCanFollow core enlarged dist R left right →
        (domainOf left).Meets (domainOf right))
    (n : ℕ) (left : ↥charts) :
    (cmp99AdmissibleTails
      (cmp99PhysicalPatchSuccessorSteps charts core enlarged dist R)
      left n).card ≤
        (S * (S + 1) * Δ ^ (2 * S)) ^ n := by
  exact card_cmp99AdmissibleTails_le_pow
    (cmp99PhysicalPatchSuccessorSteps charts core enlarged dist R)
    (S * (S + 1) * Δ ^ (2 * S))
    (fun current =>
      card_cmp99PhysicalPatchSuccessorSteps_le_simpleDomainBound
        G charts core enlarged dist R S Δ hΔ hΔ1 domainOf hinj hnear current)
    n left

end SimpleDomainDictionary

end

end YangMills.RG
