/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalFineHeadTailAnchoredLocalization
import YangMills.RG.BalabanCMP102Eq80PhysicalFineHeadTailAbsoluteBound

/-!
# Cardinality cost of a literal physical fine-head/tail domain

Every canonical equation-(80) domain is contained in the distinguished
`Pi^4` carrier together with the active carriers of the literal head and
tail walks.  Each walk of length `m` uses at most `10000 * (m + 1)` source
blocks, while the `Pi^4` carrier itself has at most `10000` blocks.

The resulting estimate turns a large physical domain into a lower bound on
the total literal walk length.  This is the combinatorial bridge needed to
convert geometric decay in the walk expansion into decay in `|Y|`.
-/

namespace YangMills.RG

noncomputable section

/-- The literal large-block carrier of `Pi^4` has at most `10000` blocks. -/
theorem card_cmp102Eq80SourcePi4AnchorCarrier_le
    {Q : ℕ} [NeZero Q] (anchor : FinBox 4 Q) :
    (cmp102Eq80SourcePi4AnchorCarrier anchor).card ≤ 10000 := by
  rw [cmp102Eq80SourcePi4AnchorCarrier,
    card_cmp99SourceDomainLargeBlocks]
  calc
    16 * (cmp99SourcePi4CollarDomain anchor).blocks.card ≤
        16 * 625 :=
      Nat.mul_le_mul_left 16
        (cmp99SourcePi4CollarDomain anchor).card_le
    _ = 10000 := by norm_num

/-- The active carrier of one literal source walk grows at most linearly
with its number of continuation steps. -/
theorem card_cmp99SourcePi4FineWalkIndex_active_le
    {M Q R walkLength : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (hrange : R + 1 ≤ 4 * M)
    (walk : CMP99SourcePi4FineWalkIndex M Q R walkLength) :
    (cmp99SourcePi4FineWalkIndex.active anchor walk).card ≤
      10000 * (walkLength + 1) := by
  have hchart :
      ∀ chart : ↥(cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q)),
        (cmp99SourceDomainLargeBlocks chart.1.domain ∩
          cmp116SourceSigmaZero anchor).card ≤ 10000 := by
    intro chart
    simpa using
      (cmp116SourceSigmaZeroPi4PhysicalChartDictionary
        (Label := Unit) anchor hrange).active_card_le chart
  have hlen :
      walk.2.1.length = walkLength :=
    length_eq_of_mem_cmp99AdmissibleTails
      (cmp99PhysicalPatchSuccessorSteps
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q))
        (cmp99SourcePi4ChartCore (M := M))
        cmp99SourcePi4ChartEnlarged physicalBondDist R)
      walk.2.2
  simpa [cmp99SourcePi4FineWalkIndex.active,
    cmp99SourcePi4FineWalkIndex.walk,
    CMP99AnchoredWalk.active, hlen] using
    ((cmp99SourcePi4FineWalkIndex.walk walk).card_active_le_mul_length_add_one
      (fun chart =>
        cmp99SourceDomainLargeBlocks chart.1.domain ∩
          cmp116SourceSigmaZero anchor)
      10000 hchart)

/-- The union of all selected tail-walk carriers is controlled by the sum
of their literal lengths. -/
theorem card_cmp99SourcePi4CoarseFineWalkChoiceActive_le
    {M Q R n : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (hrange : R + 1 ≤ 4 * M)
    {layerWord : Fin n → ℕ}
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord) :
    (cmp99SourcePi4CoarseFineWalkChoiceActive anchor choice).card ≤
      ∑ i : Fin n, 10000 * (layerWord i + 1) := by
  classical
  rw [cmp99SourcePi4CoarseFineWalkChoiceActive]
  calc
    (Finset.univ.biUnion fun i =>
        cmp99SourcePi4FineWalkIndex.active anchor (choice i)).card ≤
        ∑ i ∈ (Finset.univ : Finset (Fin n)),
          (cmp99SourcePi4FineWalkIndex.active
            anchor (choice i)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)),
          10000 * (layerWord i + 1) := by
      exact Finset.sum_le_sum fun i _hi =>
        card_cmp99SourcePi4FineWalkIndex_active_le
          anchor hrange (choice i)
    _ = ∑ i : Fin n, 10000 * (layerWord i + 1) := by
      simp

/-- The exact head-tail active carrier is controlled by the head length
and all dependent tail lengths. -/
theorem card_cmp99SourcePi4FineHeadTailActive_le
    {M Q R headLength n : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (hrange : R + 1 ≤ 4 * M)
    (head : CMP99SourcePi4FineWalkIndex M Q R headLength)
    {layerWord : Fin n → ℕ}
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord) :
    (cmp99SourcePi4FineHeadTailActive anchor head choice).card ≤
      10000 * (headLength + 1) +
        ∑ i : Fin n, 10000 * (layerWord i + 1) := by
  calc
    (cmp99SourcePi4FineHeadTailActive anchor head choice).card ≤
        (cmp99SourcePi4FineWalkIndex.active anchor head).card +
          (cmp99SourcePi4CoarseFineWalkChoiceActive anchor choice).card := by
      exact Finset.card_union_le _ _
    _ ≤ 10000 * (headLength + 1) +
          ∑ i : Fin n, 10000 * (layerWord i + 1) :=
      Nat.add_le_add
        (card_cmp99SourcePi4FineWalkIndex_active_le
          anchor hrange head)
        (card_cmp99SourcePi4CoarseFineWalkChoiceActive_le
          anchor hrange choice)

/-- A literal canonical physical domain has cardinality at most `10000`
times one anchor unit plus the total head/tail walk budget. -/
theorem card_cmp102Eq80SourcePi4FineHeadTailLocalizationDomain_le
    {M Q R headLength n : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (hrange : R + 1 ≤ 4 * M)
    (head : CMP99SourcePi4FineWalkIndex M Q R headLength)
    {layerWord : Fin n → ℕ}
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord) :
    (cmp102Eq80SourcePi4FineHeadTailLocalizationDomain
        anchor head choice).card ≤
      10000 *
        (1 + (headLength + 1) +
          ∑ i : Fin n, (layerWord i + 1)) := by
  have hsubset :=
    cmp102Eq80SourcePi4FineHeadTailLocalizationDomain_subset
      anchor head choice
  calc
    (cmp102Eq80SourcePi4FineHeadTailLocalizationDomain
        anchor head choice).card ≤
        (cmp102Eq80SourcePi4AnchorCarrier anchor ∪
          cmp99SourcePi4FineHeadTailActive anchor head choice).card :=
      Finset.card_le_card hsubset
    _ ≤ (cmp102Eq80SourcePi4AnchorCarrier anchor).card +
          (cmp99SourcePi4FineHeadTailActive
            anchor head choice).card :=
      Finset.card_union_le _ _
    _ ≤ 10000 +
        (10000 * (headLength + 1) +
          ∑ i : Fin n, 10000 * (layerWord i + 1)) :=
      Nat.add_le_add
        (card_cmp102Eq80SourcePi4AnchorCarrier_le anchor)
        (card_cmp99SourcePi4FineHeadTailActive_le
          anchor hrange head choice)
    _ = 10000 *
        (1 + (headLength + 1) +
          ∑ i : Fin n, (layerWord i + 1)) := by
      rw [← Finset.mul_sum]
      ring

end

end YangMills.RG
