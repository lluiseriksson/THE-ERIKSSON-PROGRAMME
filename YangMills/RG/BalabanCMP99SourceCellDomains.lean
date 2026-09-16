/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceBasePartition

/-!
# CMP99 domains built from the literal source partition

The vertices of the Sect. C localization graph are the partition cells `Pi`,
not the individual large blocks contained in them.  This file therefore keeps
the two levels separate:

* a simple localization domain is a face-connected family of source cells;
* its large-block carrier is the disjoint union of their order-two fibres;
* its physical bond support requires both endpoint large blocks to lie in that
  carrier.

The exact carrier cardinality is `16 * numberOfCells` in dimension four.  The
singleton source cell is also constructed as a literal simple localization
domain.  No collar width or range-protection estimate is assumed.
-/

namespace YangMills.RG

noncomputable section

/-- A single source partition cell is a nonempty face-connected simple domain
of size at most one. -/
def cmp99SourceSingletonDomain {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) :
    CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) 1 where
  blocks := {cell}
  nonempty := ⟨cell, by simp⟩
  connected := by
    intro x hx y hy
    simp only [Finset.mem_singleton] at hx hy
    subst x
    subst y
    exact ⟨SimpleGraph.Walk.nil, by simp⟩
  card_le := by simp

@[simp] theorem cmp99SourceSingletonDomain_blocks {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) :
    (cmp99SourceSingletonDomain cell).blocks = {cell} :=
  rfl

/-- Literal large-block carrier of a source simple domain. -/
noncomputable def cmp99SourceDomainLargeBlocks {Q S : ℕ} [NeZero Q]
    (X : CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S) :
    Finset (FinBox 4 (2 * Q)) :=
  X.blocks.biUnion cmp99SourceBaseCell

theorem mem_cmp99SourceDomainLargeBlocks_iff {Q S : ℕ} [NeZero Q]
    (X : CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S)
    (block : FinBox 4 (2 * Q)) :
    block ∈ cmp99SourceDomainLargeBlocks X ↔
      cmp99SourceBaseCellOwner block ∈ X.blocks := by
  classical
  constructor
  · intro hblock
    rw [cmp99SourceDomainLargeBlocks, Finset.mem_biUnion] at hblock
    obtain ⟨cell, hcell, hblock⟩ := hblock
    rw [mem_cmp99SourceBaseCell_iff] at hblock
    simpa [hblock] using hcell
  · intro howner
    rw [cmp99SourceDomainLargeBlocks, Finset.mem_biUnion]
    exact ⟨cmp99SourceBaseCellOwner block, howner,
      mem_cmp99SourceBaseCell_owner block⟩

/-- Exact dimension-four normalization of a source domain's large-block
carrier. -/
theorem card_cmp99SourceDomainLargeBlocks {Q S : ℕ} [NeZero Q]
    (X : CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S) :
    (cmp99SourceDomainLargeBlocks X).card = 16 * X.blocks.card := by
  classical
  have hdisjoint :
      (X.blocks : Set (FinBox 4 Q)).PairwiseDisjoint cmp99SourceBaseCell := by
    intro left _ right _ hne
    exact cmp99SourceBaseCells_pairwiseDisjoint
      (Finset.mem_univ left) (Finset.mem_univ right) hne
  rw [cmp99SourceDomainLargeBlocks, Finset.card_biUnion hdisjoint]
  simp [card_cmp99SourceBaseCell, Nat.mul_comm]

/-- The target source cell of a physical bond. -/
def cmp99PhysicalBondTargetBaseCell {M Q : ℕ} [NeZero M] [NeZero Q]
    (bond : PhysicalBond 4 (M * (2 * Q))) : FinBox 4 Q :=
  cmp99SourceBaseCellOwner (cmp116BondTargetBlock bond)

/-- Physical bonds supported by a source-cell domain: both endpoint large
blocks lie in cells of the domain. -/
noncomputable def cmp99SourceDomainPhysicalBondSupport {M Q S : ℕ}
    [NeZero M] [NeZero Q]
    (X : CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S) :
    Finset (PhysicalBond 4 (M * (2 * Q))) := by
  classical
  exact Finset.univ.filter fun bond =>
    cmp99PhysicalBondBaseCell bond ∈ X.blocks ∧
      cmp99PhysicalBondTargetBaseCell bond ∈ X.blocks

@[simp] theorem mem_cmp99SourceDomainPhysicalBondSupport_iff
    {M Q S : ℕ} [NeZero M] [NeZero Q]
    (X : CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S)
    (bond : PhysicalBond 4 (M * (2 * Q))) :
    bond ∈ cmp99SourceDomainPhysicalBondSupport X ↔
      cmp99PhysicalBondBaseCell bond ∈ X.blocks ∧
        cmp99PhysicalBondTargetBaseCell bond ∈ X.blocks := by
  classical
  simp [cmp99SourceDomainPhysicalBondSupport]

theorem mem_cmp99SourceDomainPhysicalBondSupport_sourceCell
    {M Q S : ℕ} [NeZero M] [NeZero Q]
    {X : CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S}
    {bond : PhysicalBond 4 (M * (2 * Q))}
    (hbond : bond ∈ cmp99SourceDomainPhysicalBondSupport X) :
    cmp99PhysicalBondBaseCell bond ∈ X.blocks :=
  (mem_cmp99SourceDomainPhysicalBondSupport_iff X bond).mp hbond |>.1

theorem mem_cmp99SourceDomainPhysicalBondSupport_targetCell
    {M Q S : ℕ} [NeZero M] [NeZero Q]
    {X : CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S}
    {bond : PhysicalBond 4 (M * (2 * Q))}
    (hbond : bond ∈ cmp99SourceDomainPhysicalBondSupport X) :
    cmp99PhysicalBondTargetBaseCell bond ∈ X.blocks :=
  (mem_cmp99SourceDomainPhysicalBondSupport_iff X bond).mp hbond |>.2

/-- A common supported physical bond forces two source-cell domains to meet. -/
theorem cmp99SourceDomains_meet_of_commonPhysicalBond
    {M Q S : ℕ} [NeZero M] [NeZero Q]
    {X Y : CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S}
    {bond : PhysicalBond 4 (M * (2 * Q))}
    (hX : bond ∈ cmp99SourceDomainPhysicalBondSupport X)
    (hY : bond ∈ cmp99SourceDomainPhysicalBondSupport Y) :
    X.Meets Y := by
  rw [CMP99SimpleLocalizationDomain.Meets, Finset.not_disjoint_iff]
  exact ⟨cmp99PhysicalBondBaseCell bond,
    mem_cmp99SourceDomainPhysicalBondSupport_sourceCell hX,
    mem_cmp99SourceDomainPhysicalBondSupport_sourceCell hY⟩

/-- The exact remaining collar condition for a base-cell core: once a source
domain contains the owner cell and the target cell of every owned bond, the
base core lies in its literal physical support. -/
theorem cmp99SourceBaseCellBondCore_subset_domainSupport
    {M Q S : ℕ} [NeZero M] [NeZero Q]
    (cell : FinBox 4 Q)
    (X : CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S)
    (hcell : cell ∈ X.blocks)
    (htarget : ∀ bond, bond ∈ cmp99SourceBaseCellBondCore (M := M) cell →
      cmp99PhysicalBondTargetBaseCell bond ∈ X.blocks) :
    cmp99SourceBaseCellBondCore (M := M) cell ⊆
      cmp99SourceDomainPhysicalBondSupport X := by
  intro bond hbond
  rw [mem_cmp99SourceDomainPhysicalBondSupport_iff]
  refine ⟨?_, htarget bond hbond⟩
  rw [mem_cmp99SourceBaseCellBondCore_iff] at hbond
  simpa [hbond] using hcell

end

end YangMills.RG
