/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4TerminalGroupedWalkLayer
import YangMills.RG.BalabanCMP99SourcePi4CorePartition
import YangMills.RG.BalabanCMP99PatchedParametrixCorePartitionWeightedRow

/-!
# Weighted-row reconstruction from terminal source groups

Once every terminal group of a fixed walk layer has a common weighted-row
bound, the exact source `Pi^4` core partition reconstructs the complete layer
with the same amplitude.  The number of quotient charts never enters.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

set_option maxHeartbeats 800000

/-- Terminal-group weighted-row bounds reconstruct the original all-head
generated layer without a chart-cardinality loss. -/
theorem cmp116SourcePi4QuotientGeneratedWalkLayer_weightedRow_of_terminalGroups
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) (n : ℕ)
    (dist : PhysicalBond 4 (M * (2 * Q)) →
      PhysicalBond 4 (M * (2 * Q)) → ℕ)
    {A rate : ℝ}
    (hA : 0 ≤ A) (hrate : 0 ≤ rate)
    (hgroup : ∀ terminal : ↥(cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)),
      PhysicalCovarianceWeightedRowKernelBound
        (cmp116SourcePi4TerminalGroupedWalkLayer
          (R := R) K hc hmass hK n terminal)
        dist A rate) :
    PhysicalCovarianceWeightedRowKernelBound
      (cmp116SourcePi4QuotientGeneratedWalkLayer
        (R := R) K hc hmass hK n)
      dist A rate := by
  rw [← sum_cmp116SourcePi4TerminalGroupedWalkLayer
    (R := R) K hc hmass hK n]
  exact physicalCovarianceWeightedRowKernelBound_sum_of_corePartition
    (d := 4) (N := M * (2 * Q)) (Nc := Nc)
    (A := A) (rate := rate)
    (charts := Finset.univ)
    (core := fun terminal : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q)) =>
        cmp99SourcePi4ChartCore (M := M) terminal.1)
    (term := cmp116SourcePi4TerminalGroupedWalkLayer
      (R := R) K hc hmass hK n)
    (dist := dist)
    hA hrate
    cmp99SourcePi4UnitChartCore_corePartition.subtype_univ
    (fun terminal _ source v hsource =>
      cmp116SourcePi4TerminalGroupedWalkLayer_apply_eq_zero_of_not_mem_core
        (R := R) K hc hmass hK n terminal source v hsource)
    (fun terminal _ => hgroup terminal)

end

end YangMills.RG
