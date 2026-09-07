/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourceSigmaZeroActiveCarrier
import YangMills.RG.BalabanCMP99SourcePi4ChartDictionary

/-!
# Local chart count for one physical weakening coordinate

For the source alphabet with the unique continuation label, a quotient-safe
`Pi^4` chart which activates one fixed large block is determined by a chosen
collar centre inside the literal radius-two collar of that block's owner.
This gives the volume-uniform constant `625`.
-/

namespace YangMills.RG

noncomputable section

/-- A deterministic representative centre of a quotient-safe source chart. -/
noncomputable def cmp99SourcePi4UnitChartChosenCenter
    {Q : ℕ} [NeZero Q]
    (chart : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q))) :
    FinBox 4 Q :=
  Classical.choose <|
    (mem_cmp99SourcePi4Domains_iff chart.1.domain).mp <|
      (mem_cmp99SourcePi4Charts_iff chart.1).mp chart.2

/-- The chosen centre generates exactly the geometric domain stored by the
chart. -/
theorem cmp99SourcePi4UnitChartChosenCenter_domain
    {Q : ℕ} [NeZero Q]
    (chart : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q))) :
    cmp99SourcePi4CollarDomain
        (cmp99SourcePi4UnitChartChosenCenter chart) =
      chart.1.domain :=
  Classical.choose_spec <|
    (mem_cmp99SourcePi4Domains_iff chart.1.domain).mp <|
      (mem_cmp99SourcePi4Charts_iff chart.1).mp chart.2

/-- With the source's unique factor label, the chosen centre is injective on
the quotient-safe chart family. -/
theorem cmp99SourcePi4UnitChartChosenCenter_injective
    {Q : ℕ} [NeZero Q] :
    Function.Injective
      (cmp99SourcePi4UnitChartChosenCenter :
        ↥(cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q)) → FinBox 4 Q) := by
  intro left right hcenter
  have hdomain : left.1.domain = right.1.domain := by
    rw [← cmp99SourcePi4UnitChartChosenCenter_domain left,
      ← cmp99SourcePi4UnitChartChosenCenter_domain right, hcenter]
  apply Subtype.ext
  cases hleft : left.1 with
  | mk leftLabel leftDomain =>
      cases hright : right.1 with
      | mk rightLabel rightDomain =>
          cases leftLabel
          cases rightLabel
          simp_all

/-- Forgetting the unique source label and retaining the quotient-safe
geometric domain is injective. -/
theorem cmp99SourcePi4UnitChart_domain_injective
    {Q : ℕ} [NeZero Q] :
    Function.Injective
      (fun chart : ↥(cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)) => chart.1.domain) := by
  intro left right hdomain
  apply Subtype.ext
  cases hleft : left.1 with
  | mk leftLabel leftDomain =>
      cases hright : right.1 with
      | mk rightLabel rightDomain =>
          cases leftLabel
          cases rightLabel
          simp_all

/-- Source charts whose literal weakening carrier activates one fixed
physical coordinate. -/
def cmp116SourcePi4CoordinatePivotCharts
    {Q : ℕ} [NeZero Q]
    (anchor : FinBox 4 Q) (pivot : FinBox 4 (2 * Q)) :
    Finset ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q)) :=
  Finset.univ.filter fun chart =>
    pivot ∈
      cmp99SourceDomainLargeBlocks chart.1.domain ∩
        cmp116SourceSigmaZero anchor

/-- The chosen centre of every chart activating `pivot` lies in the literal
radius-two source collar about the owner cell of `pivot`. -/
theorem cmp99SourcePi4UnitChartChosenCenter_mem_pivotCollar
    {Q : ℕ} [NeZero Q]
    (anchor : FinBox 4 Q) (pivot : FinBox 4 (2 * Q))
    (chart : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q)))
    (hchart : chart ∈
      cmp116SourcePi4CoordinatePivotCharts anchor pivot) :
    cmp99SourcePi4UnitChartChosenCenter chart ∈
      cmp99SourcePi4CollarCells (cmp99SourceBaseCellOwner pivot) := by
  rw [cmp116SourcePi4CoordinatePivotCharts, Finset.mem_filter] at hchart
  have hpivotLarge :
      pivot ∈ cmp99SourceDomainLargeBlocks chart.1.domain :=
    (Finset.mem_inter.mp hchart.2).1
  have hpivotOwner :
      cmp99SourceBaseCellOwner pivot ∈ chart.1.domain.blocks :=
    (mem_cmp99SourceDomainLargeBlocks_iff chart.1.domain pivot).mp
      hpivotLarge
  have hpivotInChosen :
      cmp99SourceBaseCellOwner pivot ∈
        cmp99SourcePi4CollarCells
          (cmp99SourcePi4UnitChartChosenCenter chart) := by
    rw [← cmp99SourcePi4CollarDomain_blocks]
    simpa [cmp99SourcePi4UnitChartChosenCenter_domain chart] using
      hpivotOwner
  rw [mem_cmp99SourcePi4CollarCells_iff] at hpivotInChosen ⊢
  simpa [finBoxDist_comm] using hpivotInChosen

/-- At most `625` quotient-safe source charts can activate one fixed physical
weakening coordinate, independently of the periodic volume. -/
theorem card_cmp116SourcePi4CoordinatePivotCharts_le
    {Q : ℕ} [NeZero Q]
    (anchor : FinBox 4 Q) (pivot : FinBox 4 (2 * Q)) :
    (cmp116SourcePi4CoordinatePivotCharts anchor pivot).card ≤ 625 := by
  calc
    (cmp116SourcePi4CoordinatePivotCharts anchor pivot).card ≤
        (cmp99SourcePi4CollarCells
          (cmp99SourceBaseCellOwner pivot)).card :=
      Finset.card_le_card_of_injOn
        cmp99SourcePi4UnitChartChosenCenter
        (fun chart hchart =>
          cmp99SourcePi4UnitChartChosenCenter_mem_pivotCollar
            anchor pivot chart hchart)
        (cmp99SourcePi4UnitChartChosenCenter_injective.injOn)
    _ ≤ 625 :=
      card_cmp99SourcePi4CollarCells_le
        (cmp99SourceBaseCellOwner pivot)

end

end YangMills.RG
