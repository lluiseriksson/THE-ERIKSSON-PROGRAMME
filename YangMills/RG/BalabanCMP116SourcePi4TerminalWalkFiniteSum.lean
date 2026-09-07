/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4TerminalGroupedWalkLayer
import YangMills.RG.BalabanCMP99PatchedParametrixTerminalWalkCount

/-!
# Terminal-grouped source layers as one finite walk sum

The earlier source layer is written as a double dependent sum with an
`if` selecting one terminal chart.  Here it is reindexed by the explicit
finite set of forward walks ending at that terminal.  This representation is
the one consumed by the cardinal and weighted-row estimates.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- Literal physical operator associated with one raw source walk pair. -/
noncomputable def cmp116SourcePi4ForwardWalkOperator
    {M Q Nc : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (walk : CMP99PhysicalPatchForwardWalkIndex
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))) :
    PhysicalEndomorphism M Q Nc :=
  (⟨walk.1, walk.2⟩ :
    CMP99GeneralizedWalk Unit
      ↥(cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))).term
    (cmp99PhysicalPatchHead
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK)
    (fun _ => cmp99PhysicalPatchContinuation
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK)

/-- The direct finite sum over all source walks ending at `terminal`. -/
noncomputable def cmp116SourcePi4TerminalWalkFiniteSum
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) (n : ℕ)
    (terminal : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q))) :
    PhysicalEndomorphism M Q Nc :=
  ∑ walk ∈ cmp99PhysicalPatchForwardTerminalWalks
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      (cmp99SourcePi4ChartCore (M := M))
      cmp99SourcePi4ChartEnlarged physicalBondDist R n terminal,
    cmp116SourcePi4ForwardWalkOperator K hc hmass hK walk

private theorem sourceHeadImages_pairwiseDisjoint
    {Q : ℕ} [NeZero Q]
    {M R n : ℕ} [NeZero M]
    (terminal : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q))) :
    (↑(Finset.univ :
      Finset ↥(cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))) : Set _).PairwiseDisjoint
      (fun head =>
        ((cmp99AdmissibleTails
          (cmp99PhysicalPatchSuccessorSteps
            (cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q))
            (cmp99SourcePi4ChartCore (M := M))
            cmp99SourcePi4ChartEnlarged physicalBondDist R)
          head n).filter fun tail =>
            CMP99GeneralizedWalk.terminalDomain ⟨head, tail⟩ =
              terminal).image fun tail => (head, tail)) := by
  intro left _ right _ hne
  change Disjoint
    (((cmp99AdmissibleTails
      (cmp99PhysicalPatchSuccessorSteps
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q))
        (cmp99SourcePi4ChartCore (M := M))
        cmp99SourcePi4ChartEnlarged physicalBondDist R)
      left n).filter fun tail =>
        CMP99GeneralizedWalk.terminalDomain ⟨left, tail⟩ =
          terminal).image fun tail => (left, tail))
    (((cmp99AdmissibleTails
      (cmp99PhysicalPatchSuccessorSteps
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q))
        (cmp99SourcePi4ChartCore (M := M))
        cmp99SourcePi4ChartEnlarged physicalBondDist R)
      right n).filter fun tail =>
        CMP99GeneralizedWalk.terminalDomain ⟨right, tail⟩ =
          terminal).image fun tail => (right, tail))
  rw [Finset.disjoint_left]
  intro pair hleft hright
  simp only [Finset.mem_image] at hleft hright
  obtain ⟨leftTail, _hleftTail, rfl⟩ := hleft
  obtain ⟨rightTail, _hrightTail, hEq⟩ := hright
  exact hne (congrArg Prod.fst hEq.symm)

/-- Generic terminal-walk reindexing.  Any additive summand on raw forward
walk pairs can be summed either over the explicit terminal `Finset` or over
the original dependent head/tail presentation with its terminal filter. -/
theorem sum_cmp99PhysicalPatchForwardTerminalWalks
    {E : Type*} [AddCommMonoid E]
    {M Q R n : ℕ} [NeZero M] [NeZero Q]
    (terminal : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q)))
    (F : CMP99PhysicalPatchForwardWalkIndex
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)) → E) :
    (∑ walk ∈ cmp99PhysicalPatchForwardTerminalWalks
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q))
        (cmp99SourcePi4ChartCore (M := M))
        cmp99SourcePi4ChartEnlarged physicalBondDist R n terminal,
      F walk) =
      ∑ head : ↥(cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q)),
        ∑ tail : ↥(cmp99AdmissibleTails
            (cmp99PhysicalPatchSuccessorSteps
              (cmp99SourcePi4Charts :
                Finset (CMP99SourcePi4Chart Unit Q))
              (cmp99SourcePi4ChartCore (M := M))
              cmp99SourcePi4ChartEnlarged physicalBondDist R)
            head n),
          if CMP99GeneralizedWalk.terminalDomain
              (⟨head, tail.1⟩ :
                CMP99GeneralizedWalk Unit
                  ↥(cmp99SourcePi4Charts :
                    Finset (CMP99SourcePi4Chart Unit Q))) = terminal then
            F (head, tail.1)
          else 0 := by
  classical
  rw [cmp99PhysicalPatchForwardTerminalWalks,
    Finset.sum_biUnion (sourceHeadImages_pairwiseDisjoint
      (M := M) (R := R) (n := n) terminal)]
  apply Finset.sum_congr rfl
  intro head _hhead
  rw [Finset.sum_image]
  · rw [Finset.sum_filter]
    rw [← Finset.sum_attach]
    apply Finset.sum_congr rfl
    intro tail _htail
    rfl
  · intro left _ right _ hEq
    exact congrArg Prod.snd hEq

/-- The direct terminal-walk finite sum is exactly the previously defined
terminal group of the generated source layer. -/
theorem cmp116SourcePi4TerminalWalkFiniteSum_eq_groupedWalkLayer
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) (n : ℕ)
    (terminal : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q))) :
    cmp116SourcePi4TerminalWalkFiniteSum
        (R := R) K hc hmass hK n terminal =
      cmp116SourcePi4TerminalGroupedWalkLayer
        (R := R) K hc hmass hK n terminal := by
  classical
  rw [cmp116SourcePi4TerminalWalkFiniteSum,
    cmp99PhysicalPatchForwardTerminalWalks,
    Finset.sum_biUnion (sourceHeadImages_pairwiseDisjoint
      (M := M) (R := R) (n := n) terminal)]
  simp only [cmp116SourcePi4TerminalGroupedWalkLayer]
  apply Finset.sum_congr rfl
  intro head _hhead
  rw [Finset.sum_image]
  · rw [Finset.sum_filter]
    rw [← Finset.sum_attach]
    apply Finset.sum_congr rfl
    intro tail _htail
    rfl
  · intro left _ right _ hEq
    exact congrArg Prod.snd hEq

end

end YangMills.RG
