/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116RestrictedVisitedTransferPowers

/-!
# Entrywise physical-tail expansion of restricted transfer powers

Each block of the finite visited-state transfer power is identified with the
finite sum over exactly those admissible physical tails which end at the
requested augmented state.  This strengthens the earlier row-sum identity
and permits absolute walk estimates to prove transfer-power summability
without introducing an ambient matrix-cardinality factor.
-/

namespace YangMills.RG

noncomputable section

universe u v w

/-- Final augmented state reached after one literal continuation tail. -/
def cmp116RestrictedTransferTailState
    {Label : Type u} {Domain : Type v} {Delta : Type w}
    [DecidableEq Delta]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta) :
    CMP116RestrictedTransferState Label Domain carrier →
      List (CMP99WalkStep Label Domain) →
        CMP116RestrictedTransferState Label Domain carrier
  | source, [] => source
  | source, step :: rest =>
      cmp116RestrictedTransferTailState carrier domainActive
        (cmp116RestrictedTransferNextState
          carrier domainActive source.2 step) rest

@[simp] theorem cmp116RestrictedTransferTailState_nil
    {Label : Type u} {Domain : Type v} {Delta : Type w}
    [DecidableEq Delta]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta)
    (source : CMP116RestrictedTransferState Label Domain carrier) :
    cmp116RestrictedTransferTailState carrier domainActive source [] =
      source := rfl

@[simp] theorem cmp116RestrictedTransferTailState_cons
    {Label : Type u} {Domain : Type v} {Delta : Type w}
    [DecidableEq Delta]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta)
    (source : CMP116RestrictedTransferState Label Domain carrier)
    (step : CMP99WalkStep Label Domain)
    (rest : List (CMP99WalkStep Label Domain)) :
    cmp116RestrictedTransferTailState carrier domainActive source
        (step :: rest) =
      cmp116RestrictedTransferTailState carrier domainActive
        (cmp116RestrictedTransferNextState
          carrier domainActive source.2 step) rest := rfl

/-- Direct finite sum over those admissible tails which end at one fixed
augmented target state. -/
def cmp116RestrictedVisitedGeneratedTailEntry
    {Label : Type u} {Domain : Type v} {Delta : Type w}
    [DecidableEq Label] [DecidableEq Domain] [DecidableEq Delta]
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta)
    (successors : Domain → Finset (CMP99WalkStep Label Domain))
    (R : Label → Domain → Matrix Index Index ℂ)
    (sigma : Delta → ℂ)
    (n : ℕ)
    (source target :
      CMP116RestrictedTransferState Label Domain carrier) :
    Matrix Index Index ℂ :=
  ∑ tail ∈ (cmp99AdmissibleTails successors source.1.domain n).filter
      (fun tail =>
        cmp116RestrictedTransferTailState
          carrier domainActive source tail = target),
    cmp116RestrictedVisitedTailProduct
      carrier domainActive R sigma source.2 tail

private theorem cmp99AdmissibleTailConsImages_pairwiseDisjoint'
    {Label : Type u} {Domain : Type v}
    [DecidableEq Label] [DecidableEq Domain]
    (successors : Domain → Finset (CMP99WalkStep Label Domain))
    (X : Domain) (n : ℕ) :
    (↑(successors X) : Set _).PairwiseDisjoint
      (fun step =>
        (cmp99AdmissibleTails successors step.domain n).image
          (step :: ·)) := by
  intro left _ right _ hne
  change Disjoint
    ((cmp99AdmissibleTails successors left.domain n).image
      (left :: ·))
    ((cmp99AdmissibleTails successors right.domain n).image
      (right :: ·))
  rw [Finset.disjoint_left]
  intro tail hleft hright
  simp only [Finset.mem_image] at hleft hright
  obtain ⟨leftRest, _hleftRest, rfl⟩ := hleft
  obtain ⟨rightRest, _hrightRest, hEq⟩ := hright
  exact hne (List.cons.inj hEq.symm).1

theorem cmp116RestrictedVisitedGeneratedTailEntry_succ
    {Label : Type u} {Domain : Type v} {Delta : Type w}
    [DecidableEq Label] [DecidableEq Domain] [DecidableEq Delta]
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta)
    (successors : Domain → Finset (CMP99WalkStep Label Domain))
    (R : Label → Domain → Matrix Index Index ℂ)
    (sigma : Delta → ℂ)
    (n : ℕ)
    (source target :
      CMP116RestrictedTransferState Label Domain carrier) :
    cmp116RestrictedVisitedGeneratedTailEntry
        carrier domainActive successors R sigma (n + 1) source target =
      ∑ step ∈ successors source.1.domain,
        CMP116RestrictedVisitedState.transitionWeight
            carrier sigma source.2 (domainActive step.domain) •
          (R step.label step.domain *
            cmp116RestrictedVisitedGeneratedTailEntry
              carrier domainActive successors R sigma n
              (cmp116RestrictedTransferNextState
                carrier domainActive source.2 step) target) := by
  classical
  unfold cmp116RestrictedVisitedGeneratedTailEntry
  rw [cmp99AdmissibleTails, Finset.filter_biUnion]
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro step _hstep
    rw [Finset.filter_image]
    rw [Finset.sum_image]
    · simp only [cmp116RestrictedTransferTailState_cons,
        cmp116RestrictedVisitedTailProduct]
      rw [← Finset.smul_sum, ← Finset.mul_sum]
      rfl
    · intro left _ right _ hEq
      exact (List.cons.inj hEq).2
  · intro left _ right _ hne
    have hpair :=
      cmp99AdmissibleTailConsImages_pairwiseDisjoint'
        successors source.1.domain n
    exact (hpair (by assumption) (by assumption) hne).mono
        (Finset.filter_subset _ _)
        (Finset.filter_subset _ _)

/-- Every individual block of a transfer power is the sum over precisely the
physical tails ending in that augmented state. -/
theorem cmp116RestrictedVisitedTransferMatrix_power_apply
    {Label : Type u} {Domain : Type v} {Delta : Type w}
    [Fintype Label] [Fintype Domain]
    [DecidableEq Label] [DecidableEq Domain] [DecidableEq Delta]
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta)
    (successors : Domain → Finset (CMP99WalkStep Label Domain))
    (R : Label → Domain → Matrix Index Index ℂ)
    (sigma : Delta → ℂ) :
    ∀ (n : ℕ)
      (source target :
        CMP116RestrictedTransferState Label Domain carrier),
      (cmp116RestrictedVisitedTransferMatrix
          carrier domainActive successors R sigma ^ n) source target =
        cmp116RestrictedVisitedGeneratedTailEntry
          carrier domainActive successors R sigma n source target := by
  classical
  intro n
  induction n with
  | zero =>
      intro source target
      by_cases h : source = target
      · subst target
        simp only [cmp116RestrictedVisitedGeneratedTailEntry,
          cmp99AdmissibleTails, Finset.sum_filter, Finset.sum_singleton]
        simp [cmp116RestrictedVisitedTailProduct]
      · simp only [cmp116RestrictedVisitedGeneratedTailEntry,
          cmp99AdmissibleTails, Finset.sum_filter, Finset.sum_singleton]
        simp [h]
  | succ n ih =>
      intro source target
      rw [pow_succ']
      simp_rw [Matrix.mul_apply]
      rw [cmp116RestrictedVisitedTransferMatrix_row_mul_sum]
      simp_rw [ih]
      exact
        (cmp116RestrictedVisitedGeneratedTailEntry_succ
          carrier domainActive successors R sigma n source target).symm

end

end YangMills.RG
