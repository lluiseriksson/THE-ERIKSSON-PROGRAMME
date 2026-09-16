/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourceRestrictedCoordinatePivotFirstHit
import YangMills.RG.BalabanCMP99SectionCSourcePi4ShellCardinality

/-!
# Uniform cardinality of a singleton coordinate-pivot core

Every source chart which activates one fixed large block has a collar centre
inside the literal radius-two `Pi^4` collar of that block's owner cell.  The
union of all corresponding quotient-safe chart cores is therefore contained
in a single local bond core of cardinal at most `40000 * M^4`.

This is independent of the ambient volume and of the full contour carrier.
-/

namespace YangMills.RG

noncomputable section

/-- Local bond core attached to one physical weakening coordinate. -/
def cmp116SourceCoordinatePivotBondCore
    {M Q : ℕ} [NeZero M] [NeZero Q]
    (pivot : FinBox 4 (2 * Q)) :
    Finset (PhysicalBond 4 (M * (2 * Q))) :=
  (cmp99SourcePi4CollarCells (cmp99SourceBaseCellOwner pivot)).biUnion
    (cmp99SourceBaseCellBondCore (M := M))

/-- Every bond in the singleton pivot core is indexed by a physical source
site in the literal `Pi^4` collar and one of the four positive directions. -/
theorem card_cmp116SourceCoordinatePivotBondCore_le
    {M Q : ℕ} [NeZero M] [NeZero Q]
    (pivot : FinBox 4 (2 * Q)) :
    (cmp116SourceCoordinatePivotBondCore (M := M) pivot).card ≤
      40000 * M ^ 4 := by
  classical
  let X :=
    cmp99SourcePi4CollarDomain (cmp99SourceBaseCellOwner pivot)
  let blocks := cmp99SourceDomainLargeBlocks X
  let carrier : Finset (PhysicalBond 4 (M * (2 * Q))) :=
    (cmp116RegionSites blocks) ×ˢ (Finset.univ : Finset (Fin 4))
  have hsubset :
      cmp116SourceCoordinatePivotBondCore (M := M) pivot ⊆ carrier := by
    intro bond hbond
    rw [cmp116SourceCoordinatePivotBondCore, Finset.mem_biUnion] at hbond
    obtain ⟨cell, hcell, hbond⟩ := hbond
    have hbase : cmp99PhysicalBondBaseCell bond = cell := by
      exact (mem_cmp99SourceBaseCellBondCore_iff cell bond).mp hbond
    have hsourceBlock : cmp116BondSourceBlock bond ∈ blocks := by
      dsimp [blocks]
      rw [mem_cmp99SourceDomainLargeBlocks_iff]
      change cmp99PhysicalBondBaseCell bond ∈ X.blocks
      rw [hbase]
      simpa [X, cmp99SourcePi4CollarDomain_blocks] using hcell
    exact Finset.mem_product.mpr
      ⟨mem_cmp116RegionSites_iff.mpr hsourceBlock, Finset.mem_univ _⟩
  calc
    (cmp116SourceCoordinatePivotBondCore (M := M) pivot).card ≤
        carrier.card := Finset.card_le_card hsubset
    _ = (cmp116RegionSites blocks).card * 4 := by
      rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    _ ≤ (blocks.card * M ^ 4) * 4 := by
      exact Nat.mul_le_mul_right 4 (card_cmp116RegionSites_le blocks)
    _ = ((16 * X.blocks.card) * M ^ 4) * 4 := by
      rw [show blocks.card = 16 * X.blocks.card by
        exact card_cmp99SourceDomainLargeBlocks X]
    _ ≤ ((16 * 625) * M ^ 4) * 4 := by
      gcongr
      exact X.card_le
    _ = 40000 * M ^ 4 := by ring

/-- The common first-hit core for a singleton weakening coordinate is
contained in its literal local pivot bond core. -/
theorem cmp116SourcePi4_coordinatePivot_contourActiveCore_subset
    {M Q : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q) (pivot : FinBox 4 (2 * Q)) :
    CMP99GeneralizedWalk.contourActiveCore
        (fun chart :
          ↥(cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q)) =>
          cmp99SourcePi4ChartCore (M := M) chart.1)
        (fun chart =>
          cmp99SourceDomainLargeBlocks chart.1.domain ∩
            cmp116SourceSigmaZero anchor)
        ({pivot} : Finset (FinBox 4 (2 * Q))) ⊆
      cmp116SourceCoordinatePivotBondCore (M := M) pivot := by
  classical
  intro bond hbond
  rw [CMP99GeneralizedWalk.contourActiveCore, Finset.mem_biUnion] at hbond
  obtain ⟨chart, hchart, hbond⟩ := hbond
  rw [CMP99GeneralizedWalk.contourRelevantDomains,
    Finset.mem_filter] at hchart
  have hpivot :
      pivot ∈ cmp99SourceDomainLargeBlocks chart.1.domain ∩
        cmp116SourceSigmaZero anchor := by
    simpa using hchart.2
  have hpivotLarge :
      pivot ∈ cmp99SourceDomainLargeBlocks chart.1.domain :=
    (Finset.mem_inter.mp hpivot).1
  rw [mem_cmp99SourcePi4ChartCore_iff] at hbond
  obtain ⟨center, hcenter, hbond⟩ := hbond
  have hpivotOwner :
      cmp99SourceBaseCellOwner pivot ∈ chart.1.domain.blocks := by
    exact
      (mem_cmp99SourceDomainLargeBlocks_iff chart.1.domain pivot).mp
        hpivotLarge
  have hpivotInCenter :
      cmp99SourceBaseCellOwner pivot ∈
        cmp99SourcePi4CollarCells center := by
    rw [← cmp99SourcePi4CollarDomain_blocks center]
    simpa [hcenter] using hpivotOwner
  have hcenterInPivot :
      center ∈
        cmp99SourcePi4CollarCells (cmp99SourceBaseCellOwner pivot) := by
    rw [mem_cmp99SourcePi4CollarCells_iff] at hpivotInCenter ⊢
    simpa [finBoxDist_comm] using hpivotInCenter
  rw [cmp116SourceCoordinatePivotBondCore, Finset.mem_biUnion]
  exact ⟨center, hcenterInPivot, hbond⟩

/-- Scalar coordinate dimension of the singleton first-hit core is uniformly
bounded by the local `Pi^4` geometry. -/
theorem card_cmp116SourcePi4_coordinatePivot_activeCoordinates_le
    {M Q Nc : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q) (pivot : FinBox 4 (2 * Q)) :
    (cmp116PhysicalCoreCoordinates (Nc := Nc)
      (CMP99GeneralizedWalk.contourActiveCore
        (fun chart :
          ↥(cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q)) =>
          cmp99SourcePi4ChartCore (M := M) chart.1)
        (fun chart =>
          cmp99SourceDomainLargeBlocks chart.1.domain ∩
            cmp116SourceSigmaZero anchor)
        ({pivot} : Finset (FinBox 4 (2 * Q))))).card ≤
      (40000 * M ^ 4) * (Nc ^ 2 - 1) := by
  rw [card_cmp116PhysicalCoreCoordinates]
  exact Nat.mul_le_mul_right (Nc ^ 2 - 1)
    (le_trans
      (Finset.card_le_card
        (cmp116SourcePi4_coordinatePivot_contourActiveCore_subset
          (M := M) anchor pivot))
      (card_cmp116SourceCoordinatePivotBondCore_le (M := M) pivot))

end

end YangMills.RG
