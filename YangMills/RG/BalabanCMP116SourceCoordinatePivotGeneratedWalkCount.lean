/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99FirstHitSplitEncoding
import YangMills.RG.BalabanCMP116SourceCoordinatePivotSplitCount

/-!
# Uniform count of physical walks activating one source coordinate

The exact first-hit encoding and the source `Pi^4` split count are composed.
For a fixed weakening coordinate, the head is no longer summed over the
ambient chart family: only at most `625` first-hit charts occur, and the two
complementary path pieces contribute the single branching power `K^n`.
-/

namespace YangMills.RG

noncomputable section

/-- The literal source weakening carrier of one quotient-safe `Pi^4`
chart, restricted to the `sigma = 0` sector about `anchor`. -/
def cmp116SourcePi4CoordinateActive
    {Q : ℕ} [NeZero Q] (anchor : FinBox 4 Q)
    (chart : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q))) :
    Finset (FinBox 4 (2 * Q)) :=
  cmp99SourceDomainLargeBlocks chart.1.domain ∩
    cmp116SourceSigmaZero anchor

@[simp]
theorem mem_cmp116SourcePi4CoordinateActive_iff
    {Q : ℕ} [NeZero Q] (anchor : FinBox 4 Q)
    (chart : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q)))
    (pivot : FinBox 4 (2 * Q)) :
    pivot ∈ cmp116SourcePi4CoordinateActive anchor chart ↔
      pivot ∈ cmp99SourceDomainLargeBlocks chart.1.domain ∩
        cmp116SourceSigmaZero anchor := by
  rfl

/-- Physical generated walks of length `n` which activate one fixed source
coordinate obey the differentiated uniform count
`(n+1) * 625 * K^n`. -/
theorem card_cmp116SourcePi4GeneratedWalksActivating_le
    {M Q R Delta : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q) (pivot : FinBox 4 (2 * Q))
    (hrange : R + 1 ≤ 4 * M)
    (hDelta : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Delta)
    (hDelta1 : 1 ≤ Delta)
    (n : ℕ) :
    (cmp99GeneratedWalksActivating
      (cmp99PhysicalPatchSuccessorSteps
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q))
        (cmp99SourcePi4ChartCore (M := M))
        cmp99SourcePi4ChartEnlarged physicalBondDist R)
      (cmp116SourcePi4CoordinateActive anchor) pivot n).card ≤
        (n + 1) * 625 *
          cmp116SourcePi4TerminalBranching Delta ^ n := by
  let charts :=
    (cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q))
  let core :
      CMP99SourcePi4Chart Unit Q →
        Finset (PhysicalBond 4 (M * (2 * Q))) :=
    cmp99SourcePi4ChartCore (M := M)
  let enlarged :
      CMP99SourcePi4Chart Unit Q →
        Finset (PhysicalBond 4 (M * (2 * Q))) :=
    cmp99SourcePi4ChartEnlarged
  let successors :=
    cmp99PhysicalPatchSuccessorSteps
      charts core enlarged physicalBondDist R
  let predecessors :=
    cmp99PhysicalPatchPredecessorSteps
      charts core enlarged physicalBondDist R
  have hencode :
      (cmp99GeneratedWalksActivating successors
        (cmp116SourcePi4CoordinateActive anchor) pivot n).card ≤
        (cmp99FirstHitSplitData successors predecessors
          (cmp116SourcePi4CoordinatePivotCharts anchor pivot) n).card := by
    simpa [charts, core, enlarged, successors, predecessors,
      cmp116SourcePi4CoordinatePivotCharts,
      cmp116SourcePi4CoordinateActive] using
      card_cmp99GeneratedWalksActivating_le_firstHitSplitData
        charts core enlarged physicalBondDist R
        (cmp116SourcePi4CoordinateActive anchor) pivot n
  calc
    (cmp99GeneratedWalksActivating successors
        (cmp116SourcePi4CoordinateActive anchor) pivot n).card ≤
        (cmp99FirstHitSplitData successors predecessors
          (cmp116SourcePi4CoordinatePivotCharts anchor pivot) n).card :=
      hencode
    _ ≤ (n + 1) * 625 *
        cmp116SourcePi4TerminalBranching Delta ^ n := by
      simpa [charts, core, enlarged, successors, predecessors] using
        card_cmp116SourcePi4CoordinatePivotFirstHitSplitData_le
          anchor pivot hrange hDelta hDelta1 n

end

end YangMills.RG
