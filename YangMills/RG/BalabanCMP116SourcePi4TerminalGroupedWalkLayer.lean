/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4FullWeakenedCovariance
import YangMills.RG.BalabanCMP99PatchedWalkTerminalCoreSupport

/-!
# Source `Pi^4` walk layers grouped by terminal chart

The global length layer is regrouped by the terminal chart of each generated
walk.  This is the grouping compatible with the physical core partition:
every terminal group is source-supported in one core, and summing all groups
recovers the original all-head layer exactly.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- The length-`n` physical walk layer whose terminal chart is `terminal`. -/
noncomputable def cmp116SourcePi4TerminalGroupedWalkLayer
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) (n : ℕ)
    (terminal : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q))) :
    PhysicalEndomorphism M Q Nc :=
  ∑ head : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q)),
    ∑ tail : ↥(cmp99AdmissibleTails
        (cmp99PhysicalPatchSuccessorSteps
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          (cmp99SourcePi4ChartCore (M := M))
          cmp99SourcePi4ChartEnlarged
          physicalBondDist R)
        head n),
      let walk : CMP99AnchoredWalk
          (cmp99PhysicalPatchSuccessorSteps
            (cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q))
            (cmp99SourcePi4ChartCore (M := M))
            cmp99SourcePi4ChartEnlarged
            physicalBondDist R)
          head := ⟨n, tail⟩
      if walk.toGeneralizedWalk.terminalDomain = terminal then
        walk.term
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
      else 0

/-- Summing the terminal groups gives the original all-head generated layer
exactly. -/
theorem sum_cmp116SourcePi4TerminalGroupedWalkLayer
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) (n : ℕ) :
    (∑ terminal : ↥(cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)),
      cmp116SourcePi4TerminalGroupedWalkLayer
        (R := R) K hc hmass hK n terminal) =
      cmp116SourcePi4QuotientGeneratedWalkLayer
        (R := R) K hc hmass hK n := by
  classical
  simp only [cmp116SourcePi4TerminalGroupedWalkLayer,
    cmp116SourcePi4QuotientGeneratedWalkLayer]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro head _hhead
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro tail _htail
  simp [CMP99AnchoredWalk.term]

/-- A terminal group reads only source coordinates in its terminal core. -/
theorem cmp116SourcePi4TerminalGroupedWalkLayer_apply_eq_zero_of_not_mem_core
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) (n : ℕ)
    (terminal : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q)))
    (source : PhysicalBond 4 (M * (2 * Q)))
    (v : SUNLieCoord Nc)
    (hsource :
      source ∉ cmp99SourcePi4ChartCore (M := M) terminal.1) :
    cmp116SourcePi4TerminalGroupedWalkLayer
        (R := R) K hc hmass hK n terminal
        (singlePhysicalBondCochain source v) =
      0 := by
  classical
  simp only [cmp116SourcePi4TerminalGroupedWalkLayer,
    ContinuousLinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro head _hhead
  apply Finset.sum_eq_zero
  intro tail _htail
  let walk : CMP99AnchoredWalk
      (cmp99PhysicalPatchSuccessorSteps
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q))
        (cmp99SourcePi4ChartCore (M := M))
        cmp99SourcePi4ChartEnlarged
        physicalBondDist R)
      head := ⟨n, tail⟩
  by_cases hterminal :
      walk.toGeneralizedWalk.terminalDomain = terminal
  · simp only [walk, hterminal, if_true]
    exact
      cmp99PhysicalPatchWalk_term_apply_eq_zero_of_not_mem_terminalCore
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q))
        K cmp99SourcePi4ChartEnlarged
        (cmp99SourcePi4ChartCore (M := M))
        hc hmass hK walk.toGeneralizedWalk source v
        (by simpa [hterminal] using hsource)
  · simp [walk, hterminal]

end

end YangMills.RG
