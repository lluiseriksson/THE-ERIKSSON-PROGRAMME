/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99FirstHitSplitCount
import YangMills.RG.BalabanCMP116SourceCoordinatePivotChartCount
import YangMills.RG.BalabanCMP116SourcePi4TerminalGroupedPhysicalWeightedRow
import YangMills.RG.BalabanCMP99PatchedParametrixReverseBranching

/-!
# Source `Pi^4` first-hit split count

The generic split carrier is specialized to the literal physical successor
and predecessor families.  The relevant first-hit chart count is `625` and
both directed branching families use the same source-simple-domain bound.
-/

namespace YangMills.RG

noncomputable section

/-- The physical first-hit split carrier for one source weakening
coordinate has the optimal differentiated geometric count. -/
theorem card_cmp116SourcePi4CoordinatePivotFirstHitSplitData_le
    {M Q R Delta : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q) (pivot : FinBox 4 (2 * Q))
    (hrange : R + 1 ≤ 4 * M)
    (hDelta : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Delta)
    (hDelta1 : 1 ≤ Delta)
    (n : ℕ) :
    (cmp99FirstHitSplitData
      (cmp99PhysicalPatchSuccessorSteps
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q))
        (cmp99SourcePi4ChartCore (M := M))
        cmp99SourcePi4ChartEnlarged physicalBondDist R)
      (cmp99PhysicalPatchPredecessorSteps
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q))
        (cmp99SourcePi4ChartCore (M := M))
        cmp99SourcePi4ChartEnlarged physicalBondDist R)
      (cmp116SourcePi4CoordinatePivotCharts anchor pivot) n).card ≤
        (n + 1) * 625 *
          cmp116SourcePi4TerminalBranching Delta ^ n := by
  let charts :=
    (cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q))
  let core :
      CMP99SourcePi4Chart Unit Q →
        Finset (PhysicalBond 4 (M * (2 * Q))) :=
    cmp99SourcePi4ChartCore (M := M)
  let enlarged :=
    (cmp99SourcePi4ChartEnlarged :
      CMP99SourcePi4Chart Unit Q →
        Finset (PhysicalBond 4 (M * (2 * Q))))
  let successors :=
    cmp99PhysicalPatchSuccessorSteps
      charts core enlarged physicalBondDist R
  let predecessors :=
    cmp99PhysicalPatchPredecessorSteps
      charts core enlarged physicalBondDist R
  let relevant :=
    cmp116SourcePi4CoordinatePivotCharts anchor pivot
  let branch := cmp116SourcePi4TerminalBranching Delta
  have hforward : ∀ X k,
      (cmp99AdmissibleTails successors X k).card ≤ branch ^ k := by
    intro X k
    dsimp [successors, charts, core, enlarged, branch]
    change _ ≤ (625 * 626 * Delta ^ (2 * 625)) ^ k
    exact
      card_cmp99PhysicalPatchAdmissibleTails_le_pow_simpleDomainBound
        (cmp116CoarseFaceAdj 4 Q)
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q))
        (cmp99SourcePi4ChartCore (M := M))
        cmp99SourcePi4ChartEnlarged physicalBondDist R 625 Delta
        hDelta hDelta1
        (fun chart => chart.1.domain)
        cmp99SourcePi4UnitChart_domain_injective
        (fun left right hfollow =>
          cmp99SourcePi4ChartCanFollow_implies_domainsMeet
            (M := M) (Rrange := R) hrange left.1 right.1 hfollow)
        k X
  have hreverse : ∀ X k,
      (cmp99AdmissibleTails predecessors X k).card ≤ branch ^ k := by
    intro X k
    dsimp [predecessors, charts, core, enlarged, branch]
    change _ ≤ (625 * 626 * Delta ^ (2 * 625)) ^ k
    exact
      card_cmp99PhysicalPatchReverseAdmissibleTails_le_pow_simpleDomainBound
        (cmp116CoarseFaceAdj 4 Q)
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q))
        (cmp99SourcePi4ChartCore (M := M))
        cmp99SourcePi4ChartEnlarged physicalBondDist R 625 Delta
        hDelta hDelta1
        (fun chart => chart.1.domain)
        cmp99SourcePi4UnitChart_domain_injective
        (fun left right hfollow =>
          cmp99SourcePi4ChartCanFollow_implies_domainsMeet
            (M := M) (Rrange := R) hrange left.1 right.1 hfollow)
        k X
  have hsplit :=
    card_cmp99FirstHitSplitData_le
      successors predecessors relevant branch n hforward hreverse
  calc
    (cmp99FirstHitSplitData successors predecessors relevant n).card ≤
        (n + 1) * relevant.card * branch ^ n := hsplit
    _ ≤ (n + 1) * 625 * branch ^ n := by
      gcongr
      exact card_cmp116SourcePi4CoordinatePivotCharts_le anchor pivot

end

end YangMills.RG
