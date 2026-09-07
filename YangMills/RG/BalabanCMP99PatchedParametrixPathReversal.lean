/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99PatchedParametrixReverseBranching
import YangMills.RG.BalabanCMP99PatchedParametrixAnchoredSparseWalk
import YangMills.RG.BalabanCMP99PatchedWalkTerminalCoreSupport

/-!
# Exact reversal of terminal-grouped physical patch walks

Because the physical continuation label is `Unit`, a generated tail is
determined by its ordered domains.  Reversing the complete pointed domain
path therefore converts a forward tail ending at `terminal` into a reverse
tail generated from `terminal`.
-/

namespace YangMills.RG

noncomputable section

/-- Put the unique continuation label on every domain of a list. -/
def cmp99PhysicalPatchStepsOfDomains
    {ι : Type*} {charts : Finset ι}
    (domains : List ↥charts) :
    List (CMP99WalkStep Unit ↥charts) :=
  domains.map fun domain => ⟨(), domain⟩

@[simp]
theorem map_domain_cmp99PhysicalPatchStepsOfDomains
    {ι : Type*} {charts : Finset ι}
    (domains : List ↥charts) :
    (cmp99PhysicalPatchStepsOfDomains domains).map CMP99WalkStep.domain =
      domains := by
  rw [cmp99PhysicalPatchStepsOfDomains, List.map_map]
  change List.map id domains = domains
  simp

@[simp]
theorem cmp99PhysicalPatchStepsOfDomains_map_domain
    {ι : Type*} {charts : Finset ι}
    (tail : List (CMP99WalkStep Unit ↥charts)) :
    cmp99PhysicalPatchStepsOfDomains
        (tail.map CMP99WalkStep.domain) =
      tail := by
  rw [cmp99PhysicalPatchStepsOfDomains, List.map_map]
  change List.map (fun step : CMP99WalkStep Unit ↥charts =>
    ⟨(), step.domain⟩) tail = tail
  induction tail with
  | nil => rfl
  | cons step rest ih =>
      cases step with
      | mk label domain =>
          cases label
          simp only [List.map_cons, List.cons.injEq, true_and]
          exact ih

/-- Reverse a pointed physical tail.  The terminal domain becomes the new
head, so the returned list contains the reversed path with that head removed.
-/
def cmp99ReversePhysicalPointedTail
    {ι : Type*} {charts : Finset ι}
    (head : ↥charts)
    (tail : List (CMP99WalkStep Unit ↥charts)) :
    List (CMP99WalkStep Unit ↥charts) :=
  cmp99PhysicalPatchStepsOfDomains
    ((head :: tail.map CMP99WalkStep.domain).reverse.tail)

/-- The last domain of a generalized physical walk is the last element of
its complete pointed domain path. -/
theorem getLast?_physicalPath_eq_terminalDomain
    {ι : Type*} {charts : Finset ι}
    (head : ↥charts)
    (tail : List (CMP99WalkStep Unit ↥charts)) :
    (head :: tail.map CMP99WalkStep.domain).getLast? =
      some (CMP99GeneralizedWalk.terminalDomain ⟨head, tail⟩) := by
  induction tail generalizing head with
  | nil => rfl
  | cons step rest ih =>
      simpa using ih step.domain

/-- The complete path of the reversed tail is literally the reverse of the
original complete path. -/
theorem physicalPath_reversePointedTail
    {ι : Type*} {charts : Finset ι}
    (head : ↥charts)
    (tail : List (CMP99WalkStep Unit ↥charts)) :
    CMP99GeneralizedWalk.terminalDomain ⟨head, tail⟩ ::
        (cmp99ReversePhysicalPointedTail head tail).map
          CMP99WalkStep.domain =
      (head :: tail.map CMP99WalkStep.domain).reverse := by
  rw [cmp99ReversePhysicalPointedTail,
    map_domain_cmp99PhysicalPatchStepsOfDomains]
  apply List.cons_head?_tail
  rw [List.head?_reverse, getLast?_physicalPath_eq_terminalDomain]
  simp

/-- The terminal domain of the reversed pointed path is the original head. -/
theorem terminalDomain_reversePhysicalPointedTail
    {ι : Type*} {charts : Finset ι}
    (head : ↥charts)
    (tail : List (CMP99WalkStep Unit ↥charts)) :
    CMP99GeneralizedWalk.terminalDomain
        ⟨CMP99GeneralizedWalk.terminalDomain ⟨head, tail⟩,
          cmp99ReversePhysicalPointedTail head tail⟩ =
      head := by
  have hlast :=
    getLast?_physicalPath_eq_terminalDomain
      (CMP99GeneralizedWalk.terminalDomain ⟨head, tail⟩)
      (cmp99ReversePhysicalPointedTail head tail)
  rw [physicalPath_reversePointedTail head tail,
    List.getLast?_reverse] at hlast
  simpa using hlast.symm

/-- Pointed path reversal is an involution on the tail list. -/
theorem reversePhysicalPointedTail_involutive
    {ι : Type*} {charts : Finset ι}
    (head : ↥charts)
    (tail : List (CMP99WalkStep Unit ↥charts)) :
    cmp99ReversePhysicalPointedTail
        (CMP99GeneralizedWalk.terminalDomain ⟨head, tail⟩)
        (cmp99ReversePhysicalPointedTail head tail) =
      tail := by
  have hpath :=
    physicalPath_reversePointedTail
      (CMP99GeneralizedWalk.terminalDomain ⟨head, tail⟩)
      (cmp99ReversePhysicalPointedTail head tail)
  rw [terminalDomain_reversePhysicalPointedTail head tail,
    physicalPath_reversePointedTail head tail,
    List.reverse_reverse] at hpath
  have hdomains :
      (cmp99ReversePhysicalPointedTail
          (CMP99GeneralizedWalk.terminalDomain ⟨head, tail⟩)
          (cmp99ReversePhysicalPointedTail head tail)).map
          CMP99WalkStep.domain =
        tail.map CMP99WalkStep.domain :=
    (List.cons.inj hpath).2
  calc
    cmp99ReversePhysicalPointedTail
        (CMP99GeneralizedWalk.terminalDomain ⟨head, tail⟩)
        (cmp99ReversePhysicalPointedTail head tail) =
      cmp99PhysicalPatchStepsOfDomains
        ((cmp99ReversePhysicalPointedTail
          (CMP99GeneralizedWalk.terminalDomain ⟨head, tail⟩)
          (cmp99ReversePhysicalPointedTail head tail)).map
            CMP99WalkStep.domain) :=
        (cmp99PhysicalPatchStepsOfDomains_map_domain _).symm
    _ = cmp99PhysicalPatchStepsOfDomains
        (tail.map CMP99WalkStep.domain) := by rw [hdomains]
    _ = tail := cmp99PhysicalPatchStepsOfDomains_map_domain tail

/-- Reversing a certified forward tail ending at `terminal` produces a
certified reverse tail generated from `terminal`. -/
theorem cmp99ReversePhysicalPointedTail_mem_reverseAdmissibleTails
    {ι : Type*} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core enlarged : ι → Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (R : ℕ)
    {n : ℕ} {head terminal : ↥charts}
    {tail : List (CMP99WalkStep Unit ↥charts)}
    (htail : tail ∈ cmp99AdmissibleTails
      (cmp99PhysicalPatchSuccessorSteps
        charts core enlarged dist R) head n)
    (hterminal :
      CMP99GeneralizedWalk.terminalDomain ⟨head, tail⟩ = terminal) :
    cmp99ReversePhysicalPointedTail head tail ∈
      cmp99AdmissibleTails
        (cmp99PhysicalPatchPredecessorSteps
          charts core enlarged dist R) terminal n := by
  obtain ⟨hlen, hchain⟩ :=
    (mem_cmp99AdmissibleTails_physicalPatch_iff
      charts core enlarged dist R).1 htail
  apply (mem_cmp99AdmissibleTails_physicalPatchReverse_iff
    charts core enlarged dist R).2
  constructor
  · rw [cmp99ReversePhysicalPointedTail,
      cmp99PhysicalPatchStepsOfDomains, List.length_map]
    rw [List.length_tail, List.length_reverse, List.length_cons,
      List.length_map, hlen]
    omega
  · have hpath := physicalPath_reversePointedTail head tail
    rw [hterminal] at hpath
    rw [hpath]
    exact List.isChain_reverse.2 hchain

end

end YangMills.RG
