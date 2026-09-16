/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourcePi4ChartDictionary
import YangMills.RG.BalabanCMP99PatchedParametrixCorePartition

/-!
# Exact core partition for quotient-safe source `Pi^4` charts

On small periodic tori several source cells can determine the same `Pi^4`
collar.  The source chart dictionary quotients those coincidences and unions
their owner cores.  With the unique continuation label `Unit`, those quotient
cores still form an exact partition of all physical bonds.
-/

namespace YangMills.RG

noncomputable section

/-- The quotient-safe `Pi^4` cores with the unique physical continuation
label form an exact physical core partition. -/
theorem cmp99SourcePi4UnitChartCore_corePartition
    {M Q : ℕ} [NeZero M] [NeZero Q] :
    CMP99PhysicalCorePartition
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      (cmp99SourcePi4ChartCore (M := M)) := by
  classical
  intro bond
  let owner : FinBox 4 Q := cmp99PhysicalBondBaseCell bond
  let domain : CMP99SourcePi4Domain Q :=
    cmp99SourcePi4CollarDomain owner
  let chart : CMP99SourcePi4Chart Unit Q := ⟨(), domain⟩
  refine ⟨chart, ?_, ?_, ?_⟩
  · rw [mem_cmp99SourcePi4Charts_iff]
    exact (mem_cmp99SourcePi4Domains_iff domain).2 ⟨owner, rfl⟩
  · rw [mem_cmp99SourcePi4ChartCore_iff]
    refine ⟨owner, rfl, ?_⟩
    rw [mem_cmp99SourceBaseCellBondCore_iff]
  · intro other hotherCharts hbond
    rw [mem_cmp99SourcePi4ChartCore_iff] at hbond
    obtain ⟨otherOwner, hcollar, howner⟩ := hbond
    rw [mem_cmp99SourceBaseCellBondCore_iff] at howner
    have hownerEq : otherOwner = owner := by
      exact howner.symm
    have hdomain :
        other.domain = domain := by
      rw [← hcollar, hownerEq]
    cases other with
    | mk label otherDomain =>
        cases label
        change otherDomain = domain at hdomain
        exact congrArg
          (fun X : CMP99SourcePi4Domain Q =>
            (⟨(), X⟩ : CMP99SourcePi4Chart Unit Q))
          hdomain

end

end YangMills.RG
