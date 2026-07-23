/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99PatchedParametrixPathReversal

/-!
# Counting physical forward walks with prescribed terminal chart

Forward patched walks are generated from a head chart, whereas source-core
support is controlled by their terminal chart.  This file packages all
length-`n` forward walks ending at one fixed terminal and injects them into
the reverse generated tails starting there.
-/

namespace YangMills.RG

noncomputable section

universe u

/-- A physical forward tail together with its head.  Generation membership is
stored in the finite set rather than in the type, which keeps the reversal
injection nondependent. -/
abbrev CMP99PhysicalPatchForwardWalkIndex
    {ι : Type*} (charts : Finset ι) :=
  ↥charts × List (CMP99WalkStep Unit ↥charts)

/-- All length-`n` physical forward walks whose final chart is `terminal`. -/
noncomputable def cmp99PhysicalPatchForwardTerminalWalks
    {ι : Type*} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (R n : ℕ) (terminal : ↥charts) :
    Finset (CMP99PhysicalPatchForwardWalkIndex charts) := by
  classical
  exact (Finset.univ : Finset ↥charts).biUnion fun head =>
    ((cmp99AdmissibleTails
      (cmp99PhysicalPatchSuccessorSteps
        charts core enlarged dist R)
      head n).filter fun tail =>
        CMP99GeneralizedWalk.terminalDomain ⟨head, tail⟩ = terminal).image
          fun tail => (head, tail)

/-- Forget the generation certificates and reverse the complete pointed
domain path. -/
def cmp99PhysicalPatchForwardTerminalWalkToReverseTail
    {ι : Type*}
    (charts : Finset ι)
    (walk : CMP99PhysicalPatchForwardWalkIndex charts) :
    List (CMP99WalkStep Unit ↥charts) :=
  cmp99ReversePhysicalPointedTail walk.1 walk.2

@[simp]
theorem mem_cmp99PhysicalPatchForwardTerminalWalks_iff
    {ι : Type*} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (R n : ℕ) (terminal : ↥charts)
    (walk : CMP99PhysicalPatchForwardWalkIndex charts) :
    walk ∈ cmp99PhysicalPatchForwardTerminalWalks
        charts core enlarged dist R n terminal ↔
      walk.2 ∈ cmp99AdmissibleTails
          (cmp99PhysicalPatchSuccessorSteps
            charts core enlarged dist R)
          walk.1 n ∧
        CMP99GeneralizedWalk.terminalDomain ⟨walk.1, walk.2⟩ =
          terminal := by
  classical
  rcases walk with ⟨head, tail⟩
  simp [cmp99PhysicalPatchForwardTerminalWalks]

/-- Membership in the terminal filter exposes the literal terminal-domain
identity. -/
theorem terminalDomain_eq_of_mem_cmp99PhysicalPatchForwardTerminalWalks
    {ι : Type*} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (R n : ℕ) (terminal : ↥charts)
    (walk : CMP99PhysicalPatchForwardWalkIndex charts)
    (hwalk : walk ∈ cmp99PhysicalPatchForwardTerminalWalks
      charts core enlarged dist R n terminal) :
    CMP99GeneralizedWalk.terminalDomain ⟨walk.1, walk.2⟩ =
      terminal := by
  exact (mem_cmp99PhysicalPatchForwardTerminalWalks_iff
    charts core enlarged dist R n terminal walk).1 hwalk |>.2

/-- The path-reversal map sends every terminal-filtered forward walk into
the generated reverse-tail family rooted at that terminal. -/
theorem cmp99PhysicalPatchForwardTerminalWalkToReverseTail_mapsTo
    {ι : Type*} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (R n : ℕ) (terminal : ↥charts) :
    Set.MapsTo
      (cmp99PhysicalPatchForwardTerminalWalkToReverseTail charts)
      (cmp99PhysicalPatchForwardTerminalWalks
        charts core enlarged dist R n terminal)
      (cmp99AdmissibleTails
        (cmp99PhysicalPatchPredecessorSteps
          charts core enlarged dist R)
        terminal n) := by
  intro walk hwalk
  exact cmp99ReversePhysicalPointedTail_mem_reverseAdmissibleTails
    charts core enlarged dist R
    ((mem_cmp99PhysicalPatchForwardTerminalWalks_iff
      charts core enlarged dist R n terminal walk).1 hwalk).1
    (terminalDomain_eq_of_mem_cmp99PhysicalPatchForwardTerminalWalks
      charts core enlarged dist R n terminal walk hwalk)

/-- Pointed path reversal is injective on all forward walks ending at one
fixed terminal. -/
theorem cmp99PhysicalPatchForwardTerminalWalkToReverseTail_injOn
    {ι : Type*} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (R n : ℕ) (terminal : ↥charts) :
    Set.InjOn
      (cmp99PhysicalPatchForwardTerminalWalkToReverseTail charts)
      (cmp99PhysicalPatchForwardTerminalWalks
        charts core enlarged dist R n terminal) := by
  intro left hleft right hright hEq
  have hterminalLeft :=
    terminalDomain_eq_of_mem_cmp99PhysicalPatchForwardTerminalWalks
      charts core enlarged dist R n terminal left hleft
  have hterminalRight :=
    terminalDomain_eq_of_mem_cmp99PhysicalPatchForwardTerminalWalks
      charts core enlarged dist R n terminal right hright
  have hheadLeft :=
    terminalDomain_reversePhysicalPointedTail left.1 left.2
  have hheadRight :=
    terminalDomain_reversePhysicalPointedTail right.1 right.2
  rw [hterminalLeft] at hheadLeft
  rw [hterminalRight] at hheadRight
  change cmp99ReversePhysicalPointedTail left.1 left.2 =
    cmp99ReversePhysicalPointedTail right.1 right.2 at hEq
  rw [hEq] at hheadLeft
  have hhead : left.1 = right.1 :=
    hheadLeft.symm.trans hheadRight
  have htailLeft :=
    reversePhysicalPointedTail_involutive left.1 left.2
  have htailRight :=
    reversePhysicalPointedTail_involutive right.1 right.2
  rw [hterminalLeft] at htailLeft
  rw [hterminalRight] at htailRight
  rw [hEq] at htailLeft
  have htail : left.2 = right.2 :=
    htailLeft.symm.trans htailRight
  exact Prod.ext hhead htail

/-- Forward walks ending at `terminal` are no more numerous than the reverse
generated tails starting there. -/
theorem card_cmp99PhysicalPatchForwardTerminalWalks_le_reverseTails
    {ι : Type*} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (R n : ℕ) (terminal : ↥charts) :
    (cmp99PhysicalPatchForwardTerminalWalks
      charts core enlarged dist R n terminal).card ≤
      (cmp99AdmissibleTails
        (cmp99PhysicalPatchPredecessorSteps
          charts core enlarged dist R)
        terminal n).card := by
  exact Finset.card_le_card_of_injOn
    (cmp99PhysicalPatchForwardTerminalWalkToReverseTail charts)
    (cmp99PhysicalPatchForwardTerminalWalkToReverseTail_mapsTo
      charts core enlarged dist R n terminal)
    (cmp99PhysicalPatchForwardTerminalWalkToReverseTail_injOn
      charts core enlarged dist R n terminal)

section SimpleDomainDictionary

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Final uniform bound for all physical length-`n` forward walks ending at
one prescribed terminal chart. -/
theorem card_cmp99PhysicalPatchForwardTerminalWalks_le_pow_simpleDomainBound
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
    (cmp99PhysicalPatchForwardTerminalWalks
      charts core enlarged dist R n terminal).card ≤
        (S * (S + 1) * Δ ^ (2 * S)) ^ n :=
  (card_cmp99PhysicalPatchForwardTerminalWalks_le_reverseTails
    charts core enlarged dist R n terminal).trans
      (card_cmp99PhysicalPatchReverseAdmissibleTails_le_pow_simpleDomainBound
        G charts core enlarged dist R S Δ hΔ hΔ1
        domainOf hinj hnear n terminal)

end SimpleDomainDictionary

end

end YangMills.RG
