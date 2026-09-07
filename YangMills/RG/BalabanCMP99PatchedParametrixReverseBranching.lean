/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99PatchedParametrixSparseWalkBranching

/-!
# Reverse branching for terminal-grouped patched walks

The physical continuation relation is directed because it compares the left
core with the right enlarged collar.  Nevertheless, the source-domain
dictionary sends every surviving transition to two meeting simple domains.
Since meeting is symmetric, the same lattice-animal count bounds the number
of predecessors of a fixed terminal chart.
-/

namespace YangMills.RG

noncomputable section

universe u

/-- Physical charts that can precede a fixed right chart. -/
noncomputable def cmp99PhysicalPatchPredecessors
    {ι : Type*} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (R : ℕ)
    (right : ↥charts) : Finset ↥charts := by
  classical
  exact Finset.univ.filter fun left =>
    CMP99PhysicalPatchCanFollow core enlarged dist R left right

@[simp]
theorem mem_cmp99PhysicalPatchPredecessors_iff
    {ι : Type*} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (R : ℕ)
    (left right : ↥charts) :
    left ∈ cmp99PhysicalPatchPredecessors
        charts core enlarged dist R right ↔
      CMP99PhysicalPatchCanFollow core enlarged dist R left right := by
  simp [cmp99PhysicalPatchPredecessors]

/-- Add the unique continuation label to the predecessor family. -/
noncomputable def cmp99PhysicalPatchPredecessorSteps
    {ι : Type*} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (R : ℕ)
    (right : ↥charts) :
    Finset (CMP99WalkStep Unit ↥charts) :=
  (cmp99PhysicalPatchPredecessors charts core enlarged dist R right).image
    fun left => ⟨(), left⟩

@[simp]
theorem mem_cmp99PhysicalPatchPredecessorSteps_iff
    {ι : Type*} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (R : ℕ)
    (right : ↥charts) (step : CMP99WalkStep Unit ↥charts) :
    step ∈ cmp99PhysicalPatchPredecessorSteps
        charts core enlarged dist R right ↔
      CMP99PhysicalPatchCanFollow core enlarged dist R step.domain right := by
  constructor
  · intro hstep
    simp only [cmp99PhysicalPatchPredecessorSteps,
      Finset.mem_image] at hstep
    obtain ⟨left, hleft, hEq⟩ := hstep
    cases step
    cases hEq
    exact (mem_cmp99PhysicalPatchPredecessors_iff
      charts core enlarged dist R left right).mp hleft
  · intro hnear
    rw [cmp99PhysicalPatchPredecessorSteps, Finset.mem_image]
    refine ⟨step.domain, ?_, ?_⟩
    · exact (mem_cmp99PhysicalPatchPredecessors_iff
        charts core enlarged dist R step.domain right).mpr hnear
    · cases step with
      | mk label domain =>
          cases label
          rfl

section SimpleDomainDictionary

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The domains of all predecessors of `right` lie among the simple domains
meeting the domain of `right`. -/
theorem image_cmp99PhysicalPatchPredecessors_subset_meetingSimpleDomains
    {ι : Type*} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (R S : ℕ)
    (domainOf : ↥charts → CMP99SimpleLocalizationDomain G S)
    (hnear : ∀ (left right : ↥charts),
      CMP99PhysicalPatchCanFollow core enlarged dist R left right →
        (domainOf left).Meets (domainOf right))
    (right : ↥charts) :
    (cmp99PhysicalPatchPredecessors charts core enlarged dist R right).image
        domainOf ⊆
      cmp99MeetingSimpleDomains G S (domainOf right) := by
  intro domain hdomain
  simp only [Finset.mem_image] at hdomain
  obtain ⟨left, hleft, rfl⟩ := hdomain
  rw [cmp99MeetingSimpleDomains, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have hmeet := hnear left right
    ((mem_cmp99PhysicalPatchPredecessors_iff
      charts core enlarged dist R left right).mp hleft)
  intro hdisjoint
  exact hmeet hdisjoint.symm

/-- Explicit volume-uniform bound for all charts that can precede a fixed
terminal chart. -/
theorem card_cmp99PhysicalPatchPredecessors_le_simpleDomainBound
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
    (right : ↥charts) :
    (cmp99PhysicalPatchPredecessors
      charts core enlarged dist R right).card ≤
        S * (S + 1) * Δ ^ (2 * S) := by
  calc
    (cmp99PhysicalPatchPredecessors
        charts core enlarged dist R right).card =
      ((cmp99PhysicalPatchPredecessors
          charts core enlarged dist R right).image domainOf).card := by
        symm
        exact Finset.card_image_of_injective _ hinj
    _ ≤ (cmp99MeetingSimpleDomains G S (domainOf right)).card :=
      Finset.card_le_card
        (image_cmp99PhysicalPatchPredecessors_subset_meetingSimpleDomains
          G charts core enlarged dist R S domainOf hnear right)
    _ ≤ S * (S + 1) * Δ ^ (2 * S) :=
      card_cmp99MeetingSimpleDomains_le G S Δ hΔ hΔ1 (domainOf right)

/-- The same bound for the uniquely labelled reverse steps. -/
theorem card_cmp99PhysicalPatchPredecessorSteps_le_simpleDomainBound
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
    (right : ↥charts) :
    (cmp99PhysicalPatchPredecessorSteps
      charts core enlarged dist R right).card ≤
        S * (S + 1) * Δ ^ (2 * S) := by
  rw [cmp99PhysicalPatchPredecessorSteps,
    Finset.card_image_of_injective]
  · exact card_cmp99PhysicalPatchPredecessors_le_simpleDomainBound
      G charts core enlarged dist R S Δ hΔ hΔ1
      domainOf hinj hnear right
  · intro left₁ left₂ hEq
    exact congrArg CMP99WalkStep.domain hEq

/-- Reverse tails generated from a terminal chart satisfy the literal
backward chain: every new domain can physically precede the current one. -/
theorem chain_of_mem_cmp99PhysicalPatchReverseAdmissibleTails
    {ι : Type*} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (R : ℕ) :
    ∀ {n terminal tail},
      tail ∈ cmp99AdmissibleTails
        (cmp99PhysicalPatchPredecessorSteps
          charts core enlarged dist R)
        terminal n →
      (terminal :: tail.map CMP99WalkStep.domain).IsChain
        (fun (right left : ↥charts) =>
          CMP99PhysicalPatchCanFollow core enlarged dist R left right) := by
  exact chain_of_mem_cmp99AdmissibleTails
    (cmp99PhysicalPatchPredecessorSteps
      charts core enlarged dist R)
    (fun right left =>
      CMP99PhysicalPatchCanFollow core enlarged dist R left right)
    (fun right step hstep =>
      (mem_cmp99PhysicalPatchPredecessorSteps_iff
        charts core enlarged dist R right step).mp hstep)

/-- Reverse generated tails are characterized exactly by their length and
the backward physical chain. -/
theorem mem_cmp99AdmissibleTails_physicalPatchReverse_iff
    {ι : Type*} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (R : ℕ) :
    ∀ {n : ℕ} {terminal : ↥charts}
      {tail : List (CMP99WalkStep Unit ↥charts)},
      tail ∈ cmp99AdmissibleTails
          (cmp99PhysicalPatchPredecessorSteps
            charts core enlarged dist R) terminal n ↔
        tail.length = n ∧
          (terminal :: tail.map CMP99WalkStep.domain).IsChain
            (fun right left : ↥charts =>
              CMP99PhysicalPatchCanFollow core enlarged dist R left right) := by
  intro n
  induction n with
  | zero =>
      intro terminal tail
      constructor
      · intro htail
        have hnil : tail = [] := by
          simpa [cmp99AdmissibleTails] using htail
        subst hnil
        simp
      · rintro ⟨hlen, _hchain⟩
        have hnil : tail = [] := List.eq_nil_of_length_eq_zero hlen
        subst hnil
        simp [cmp99AdmissibleTails]
  | succ n ih =>
      intro terminal tail
      constructor
      · intro htail
        exact ⟨
          length_eq_of_mem_cmp99AdmissibleTails
            (cmp99PhysicalPatchPredecessorSteps
              charts core enlarged dist R) htail,
          chain_of_mem_cmp99PhysicalPatchReverseAdmissibleTails
            charts core enlarged dist R htail⟩
      · rintro ⟨hlen, hchain⟩
        cases tail with
        | nil => simp at hlen
        | cons step rest =>
            rw [cmp99AdmissibleTails, Finset.mem_biUnion]
            refine ⟨step, ?_, ?_⟩
            · rw [mem_cmp99PhysicalPatchPredecessorSteps_iff]
              exact hchain.rel_head
            · rw [Finset.mem_image]
              refine ⟨rest, ?_, rfl⟩
              apply (ih (terminal := step.domain) (tail := rest)).2
              constructor
              · simpa using hlen
              · simpa using hchain.tail

/-- The number of length-`n` reverse tails ending at a prescribed physical
terminal chart obeys the same volume-uniform lattice-animal branching bound
as the forward source tails. -/
theorem card_cmp99PhysicalPatchReverseAdmissibleTails_le_pow_simpleDomainBound
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
    (n : ℕ) (terminal : ↥charts) :
    (cmp99AdmissibleTails
      (cmp99PhysicalPatchPredecessorSteps
        charts core enlarged dist R)
      terminal n).card ≤
        (S * (S + 1) * Δ ^ (2 * S)) ^ n := by
  exact card_cmp99AdmissibleTails_le_pow
    (cmp99PhysicalPatchPredecessorSteps
      charts core enlarged dist R)
    (S * (S + 1) * Δ ^ (2 * S))
    (fun current =>
      card_cmp99PhysicalPatchPredecessorSteps_le_simpleDomainBound
        G charts core enlarged dist R S Δ hΔ hΔ1
        domainOf hinj hnear current)
    n terminal

end SimpleDomainDictionary

end

end YangMills.RG
