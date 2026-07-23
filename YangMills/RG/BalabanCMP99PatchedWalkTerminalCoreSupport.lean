/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99PatchedParametrixAnchoredSparseWalk

/-!
# Terminal-core support of physical patched walks

The source coordinate of the ordered CMP99 product is read by its rightmost
operator.  Hence a nonempty walk is source-supported in the core of its
terminal chart, not in the distinguished head chart.

This orientation is load-bearing when all heads are summed: grouping by the
terminal chart allows the exact core partition to remove any factor equal to
the total number of charts.
-/

namespace YangMills.RG

noncomputable section

universe u v

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- Last domain visited by a generalized walk, with the head as the terminal
domain of a length-zero walk. -/
def CMP99GeneralizedWalk.terminalDomain
    {Label : Type u} {Domain : Type v}
    (walk : CMP99GeneralizedWalk Label Domain) : Domain :=
  walk.tail.foldl (fun _ step => step.domain) walk.head

@[simp]
theorem CMP99GeneralizedWalk.terminalDomain_nil
    {Label : Type u} {Domain : Type v} (head : Domain) :
    (CMP99GeneralizedWalk.terminalDomain
      (⟨head, []⟩ : CMP99GeneralizedWalk Label Domain)) = head := by
  rfl

@[simp]
theorem CMP99GeneralizedWalk.terminalDomain_cons
    {Label : Type u} {Domain : Type v}
    (head : Domain) (step : CMP99WalkStep Label Domain)
    (tail : List (CMP99WalkStep Label Domain)) :
    CMP99GeneralizedWalk.terminalDomain ⟨head, step :: tail⟩ =
      CMP99GeneralizedWalk.terminalDomain ⟨step.domain, tail⟩ := by
  rfl

private theorem orderedPhysicalProduct_apply_eq_zero_of_terminalCore
    {Label : Type u} {Domain : Type v}
    {d N Nc : ℕ} [NeZero N]
    (core : Domain → Finset (PhysicalBond d N))
    (R : Label → Domain → PhysicalEndomorphism d N Nc)
    (head : Domain) (headOp : PhysicalEndomorphism d N Nc)
    (tail : List (CMP99WalkStep Label Domain))
    (hhead : ∀ source (v : SUNLieCoord Nc),
      source ∉ core head →
        headOp (singlePhysicalBondCochain source v) = 0)
    (hR : ∀ label domain source (v : SUNLieCoord Nc),
      source ∉ core domain →
        R label domain (singlePhysicalBondCochain source v) = 0)
    (source : PhysicalBond d N) (v : SUNLieCoord Nc)
    (hsource :
      source ∉ core
        (CMP99GeneralizedWalk.terminalDomain
          (⟨head, tail⟩ : CMP99GeneralizedWalk Label Domain))) :
    (headOp :: tail.map (fun step => R step.label step.domain)).prod
        (singlePhysicalBondCochain source v) = 0 := by
  induction tail generalizing head headOp with
  | nil =>
      simpa using hhead source v hsource
  | cons step rest ih =>
      have htail :
          (R step.label step.domain ::
              rest.map (fun next => R next.label next.domain)).prod
              (singlePhysicalBondCochain source v) = 0 := by
        apply ih step.domain (R step.label step.domain)
        · intro q w hq
          exact hR step.label step.domain q w hq
        · simpa using hsource
      change headOp
        ((R step.label step.domain ::
          rest.map (fun next => R next.label next.domain)).prod
            (singlePhysicalBondCochain source v)) = 0
      rw [htail, map_zero]

/-- A generalized ordered product is source-supported in its terminal core. -/
theorem CMP99GeneralizedWalk.term_apply_eq_zero_of_not_mem_terminalCore
    {Label : Type u} {Domain : Type v}
    {d N Nc : ℕ} [NeZero N]
    (core : Domain → Finset (PhysicalBond d N))
    (R0 : Domain → PhysicalEndomorphism d N Nc)
    (R : Label → Domain → PhysicalEndomorphism d N Nc)
    (hR0 : ∀ domain source (v : SUNLieCoord Nc),
      source ∉ core domain →
        R0 domain (singlePhysicalBondCochain source v) = 0)
    (hR : ∀ label domain source (v : SUNLieCoord Nc),
      source ∉ core domain →
        R label domain (singlePhysicalBondCochain source v) = 0)
    (walk : CMP99GeneralizedWalk Label Domain)
    (source : PhysicalBond d N) (v : SUNLieCoord Nc)
    (hsource : source ∉ core walk.terminalDomain) :
    walk.term R0 R (singlePhysicalBondCochain source v) = 0 := by
  exact orderedPhysicalProduct_apply_eq_zero_of_terminalCore
    core R walk.head (R0 walk.head) walk.tail
    (hR0 walk.head) hR source v hsource

/-- A physical patched head reads only its own core coordinates. -/
theorem cmp99PhysicalPatchHead_apply_eq_zero_of_not_mem_core
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι)
    (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (i : ↥charts) (source : PhysicalBond d N) (v : SUNLieCoord Nc)
    (hsource : source ∉ core i) :
    cmp99PhysicalPatchHead charts K enlarged core hc hmass hK i
        (singlePhysicalBondCochain source v) = 0 := by
  simp [cmp99PhysicalPatchHead, ContinuousLinearMap.comp_apply,
    physicalBondProjection_single_not_mem _ _ _ hsource]

/-- A physical patched continuation also reads only its own core
coordinates. -/
theorem cmp99PhysicalPatchContinuation_apply_eq_zero_of_not_mem_core
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι)
    (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (i : ↥charts) (source : PhysicalBond d N) (v : SUNLieCoord Nc)
    (hsource : source ∉ core i) :
    cmp99PhysicalPatchContinuation charts K enlarged core hc hmass hK i
        (singlePhysicalBondCochain source v) = 0 := by
  simp [cmp99PhysicalPatchContinuation,
    physicalBondProjection_single_not_mem _ _ _ hsource]

/-- Literal physical patched walks are source-supported in the core of their
terminal chart. -/
theorem cmp99PhysicalPatchWalk_term_apply_eq_zero_of_not_mem_terminalCore
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι)
    (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (walk : CMP99GeneralizedWalk Unit ↥charts)
    (source : PhysicalBond d N) (v : SUNLieCoord Nc)
    (hsource : source ∉ core walk.terminalDomain) :
    walk.term
        (cmp99PhysicalPatchHead charts K enlarged core hc hmass hK)
        (fun _ => cmp99PhysicalPatchContinuation
          charts K enlarged core hc hmass hK)
        (singlePhysicalBondCochain source v) = 0 := by
  exact walk.term_apply_eq_zero_of_not_mem_terminalCore
    (fun i : ↥charts => core i)
    (cmp99PhysicalPatchHead charts K enlarged core hc hmass hK)
    (fun _ => cmp99PhysicalPatchContinuation
      charts K enlarged core hc hmass hK)
    (fun domain q w hq =>
      cmp99PhysicalPatchHead_apply_eq_zero_of_not_mem_core
        charts K enlarged core hc hmass hK domain q w hq)
    (fun _label domain q w hq =>
      cmp99PhysicalPatchContinuation_apply_eq_zero_of_not_mem_core
        charts K enlarged core hc hmass hK domain q w hq)
    source v hsource

end

end YangMills.RG
