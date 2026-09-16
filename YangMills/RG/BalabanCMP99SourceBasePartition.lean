/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99CanonicalCoreOwnership
import YangMills.RG.BalabanCMP116Eq219SourceGeometry

/-!
# The literal CMP99 base-cell partition

Section C of CMP99 partitions the coarse lattice into cubes `Pi`, each made
of `2^d` large blocks.  In dimension four the source base cell containing a
large block is therefore the fibre of the order-two block map and has exactly
`2^4 = 16` members.

This file records that geometry literally on the periodic lattice.  It proves
that every large block has a unique base-cell owner and transports the same
ownership to physical bonds through their source large block.  The resulting
bond cores form an exact `CMP99PhysicalCorePartition` and, in particular, a
`CMP99PhysicalCoreCover`.

This is the source partition, not yet the CMP99 localization collar.  A later
module must enlarge these cells by the printed collar width, prove connected
small-domain bounds, and show that the enlarged domain protects the required
interaction range.  No such coverage is assumed here.
-/

namespace YangMills.RG

noncomputable section

/-- The CMP99 base cell containing a large block: coordinatewise division by
two on the large-block lattice. -/
def cmp99SourceBaseCellOwner {Q : ℕ} [NeZero Q]
    (block : FinBox 4 (2 * Q)) : FinBox 4 Q :=
  blockSite 2 Q block

/-- The literal source cube `Pi`: the sixteen large blocks with the same
order-two block owner. -/
noncomputable def cmp99SourceBaseCell {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) : Finset (FinBox 4 (2 * Q)) :=
  blockOf 2 Q cell

@[simp] theorem mem_cmp99SourceBaseCell_iff {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) (block : FinBox 4 (2 * Q)) :
    block ∈ cmp99SourceBaseCell cell ↔
      cmp99SourceBaseCellOwner block = cell := by
  exact mem_blockOf 2 Q cell block

/-- Every large block belongs to the base cell selected by its literal block
owner. -/
theorem mem_cmp99SourceBaseCell_owner {Q : ℕ} [NeZero Q]
    (block : FinBox 4 (2 * Q)) :
    block ∈ cmp99SourceBaseCell (cmp99SourceBaseCellOwner block) := by
  rw [mem_cmp99SourceBaseCell_iff]

/-- Source base cells have the printed dimension-four cardinality `2^4`. -/
@[simp] theorem card_cmp99SourceBaseCell {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) :
    (cmp99SourceBaseCell cell).card = 16 := by
  simpa [cmp99SourceBaseCell] using
    (blockOf_card (d := 4) 2 Q cell)

/-- A large block cannot belong to two distinct source base cells. -/
theorem cmp99SourceBaseCell_unique {Q : ℕ} [NeZero Q]
    {left right : FinBox 4 Q} {block : FinBox 4 (2 * Q)}
    (hleft : block ∈ cmp99SourceBaseCell left)
    (hright : block ∈ cmp99SourceBaseCell right) :
    left = right := by
  rw [mem_cmp99SourceBaseCell_iff] at hleft hright
  exact hleft.symm.trans hright

/-- The source cells are pairwise disjoint fibres of the order-two block
map. -/
theorem cmp99SourceBaseCells_pairwiseDisjoint {Q : ℕ} [NeZero Q] :
    ((Finset.univ : Finset (FinBox 4 Q)) : Set (FinBox 4 Q)).PairwiseDisjoint
      cmp99SourceBaseCell := by
  intro left _ right _ hne
  change Disjoint (cmp99SourceBaseCell left) (cmp99SourceBaseCell right)
  rw [Finset.disjoint_left]
  intro block hleft hright
  exact hne (cmp99SourceBaseCell_unique hleft hright)

/-- The union of all source cells is the complete large-block lattice. -/
theorem biUnion_cmp99SourceBaseCell_eq_univ {Q : ℕ} [NeZero Q] :
    (Finset.univ : Finset (FinBox 4 Q)).biUnion cmp99SourceBaseCell =
      (Finset.univ : Finset (FinBox 4 (2 * Q))) := by
  classical
  ext block
  constructor
  · intro _
    exact Finset.mem_univ block
  · intro _
    rw [Finset.mem_biUnion]
    exact ⟨cmp99SourceBaseCellOwner block, Finset.mem_univ _,
      mem_cmp99SourceBaseCell_owner block⟩

/-- The base cell of a physical bond is the source `Pi` containing its source
large block. -/
def cmp99PhysicalBondBaseCell {M Q : ℕ} [NeZero M] [NeZero Q]
    (bond : PhysicalBond 4 (M * (2 * Q))) : FinBox 4 Q :=
  cmp99SourceBaseCellOwner (cmp116BondSourceBlock bond)

/-- Physical bonds assigned to one source base cell.  Assignment by source
block is literal and deterministic; the later collar contains both endpoints
and the whole finite interaction neighbourhood. -/
noncomputable def cmp99SourceBaseCellBondCore {M Q : ℕ}
    [NeZero M] [NeZero Q] (cell : FinBox 4 Q) :
    Finset (PhysicalBond 4 (M * (2 * Q))) := by
  classical
  exact Finset.univ.filter fun bond =>
    cmp99PhysicalBondBaseCell bond = cell

@[simp] theorem mem_cmp99SourceBaseCellBondCore_iff {M Q : ℕ}
    [NeZero M] [NeZero Q] (cell : FinBox 4 Q)
    (bond : PhysicalBond 4 (M * (2 * Q))) :
    bond ∈ cmp99SourceBaseCellBondCore cell ↔
      cmp99PhysicalBondBaseCell bond = cell := by
  classical
  simp [cmp99SourceBaseCellBondCore]

/-- The literal base-cell bond cores cover every physical bond. -/
theorem cmp99SourceBaseCellBondCore_cover {M Q : ℕ}
    [NeZero M] [NeZero Q] :
    CMP99PhysicalCoreCover (Finset.univ : Finset (FinBox 4 Q))
      (cmp99SourceBaseCellBondCore (M := M)) := by
  intro bond
  refine ⟨cmp99PhysicalBondBaseCell bond, Finset.mem_univ _, ?_⟩
  rw [mem_cmp99SourceBaseCellBondCore_iff]

/-- Stronger than coverage: the source-base bond cores form an exact physical
partition. -/
theorem cmp99SourceBaseCellBondCore_corePartition {M Q : ℕ}
    [NeZero M] [NeZero Q] :
    CMP99PhysicalCorePartition (Finset.univ : Finset (FinBox 4 Q))
      (cmp99SourceBaseCellBondCore (M := M)) := by
  intro bond
  refine ⟨cmp99PhysicalBondBaseCell bond, Finset.mem_univ _, ?_, ?_⟩
  · rw [mem_cmp99SourceBaseCellBondCore_iff]
  · intro cell _ hcell
    rw [mem_cmp99SourceBaseCellBondCore_iff] at hcell
    exact hcell.symm

end

end YangMills.RG
