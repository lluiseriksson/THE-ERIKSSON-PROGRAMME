/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4TerminalWalkFiniteSum
import YangMills.RG.BalabanCMP99PivotedGeneratedWalk

/-!
# Reindex terminal groups by generated source walks

The terminal chart is determined by a generated physical walk.  Summing all
terminal groups therefore counts each head/tail pair exactly once.  If a
summand vanishes off one marked coordinate carrier, the same sum can be
restricted exactly to the marked generated-walk `Finset`.
-/

namespace YangMills.RG

noncomputable section

/-- All terminal-filtered physical walks of one length reindex exactly as
the sigma type of generated head/tail pairs. -/
theorem sum_sourceTerminalWalks_eq_sum_generatedWalks
    {E : Type*} [AddCommMonoid E]
    {M Q R n : ℕ} [NeZero M] [NeZero Q]
    (F : CMP99PhysicalPatchForwardWalkIndex
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)) → E) :
    (∑ terminal : ↥(cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)),
      ∑ walk ∈ cmp99PhysicalPatchForwardTerminalWalks
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          (cmp99SourcePi4ChartCore (M := M))
          cmp99SourcePi4ChartEnlarged physicalBondDist R n terminal,
        F walk) =
      ∑ walk : CMP99GeneratedWalkAtLength
          (cmp99PhysicalPatchSuccessorSteps
            (cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q))
            (cmp99SourcePi4ChartCore (M := M))
            cmp99SourcePi4ChartEnlarged physicalBondDist R) n,
        F (walk.1, walk.2.1) := by
  classical
  simp_rw [sum_cmp99PhysicalPatchForwardTerminalWalks
    (M := M) (R := R) (n := n)]
  rw [Fintype.sum_sigma]
  simp only
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro head _hhead
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro tail _htail
  simp

/-- If the physical summand vanishes outside one marked weakening
coordinate, the complete terminal sum is exactly the sum over generated
walks which activate that coordinate. -/
theorem sum_sourceTerminalWalks_eq_sum_generatedWalksActivating
    {E : Type*} [AddCommMonoid E] {Cube : Type*} [DecidableEq Cube]
    {M Q R n : ℕ} [NeZero M] [NeZero Q]
    (domainActive :
      ↥(cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)) → Finset Cube)
    (pivot : Cube)
    (F : CMP99PhysicalPatchForwardWalkIndex
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)) → E)
    (hzero : ∀ walk :
      CMP99GeneratedWalkAtLength
        (cmp99PhysicalPatchSuccessorSteps
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          (cmp99SourcePi4ChartCore (M := M))
          cmp99SourcePi4ChartEnlarged physicalBondDist R) n,
      pivot ∉ walk.toGeneralizedWalk.active domainActive →
        F (walk.1, walk.2.1) = 0) :
    (∑ terminal : ↥(cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)),
      ∑ walk ∈ cmp99PhysicalPatchForwardTerminalWalks
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          (cmp99SourcePi4ChartCore (M := M))
          cmp99SourcePi4ChartEnlarged physicalBondDist R n terminal,
        F walk) =
      ∑ walk ∈ cmp99GeneratedWalksActivating
          (cmp99PhysicalPatchSuccessorSteps
            (cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q))
            (cmp99SourcePi4ChartCore (M := M))
            cmp99SourcePi4ChartEnlarged physicalBondDist R)
          domainActive pivot n,
        F (walk.1, walk.2.1) := by
  classical
  rw [sum_sourceTerminalWalks_eq_sum_generatedWalks (M := M) (R := R)]
  rw [cmp99GeneratedWalksActivating, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro walk _hwalk
  by_cases hactive :
      pivot ∈ walk.toGeneralizedWalk.active domainActive
  · simp [hactive]
  · simp [hactive, hzero walk hactive]

end

end YangMills.RG
