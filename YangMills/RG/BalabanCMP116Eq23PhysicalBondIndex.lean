/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214LocalizationCore

/-!
# CMP116 equation (2.3): the physical bond index `P ⊆ Y₀^{c,*}`

CMP116 printed page 12 defines `Y₀ = ⋃_{Y∈D} Y` and then sums over bond
sets `P` contained in `Y₀^{c,*}`, after removing the distinguished bonds
`b₀(c)`.  This module connects that source statement to the periodic physical
bond type.

A physical bond belongs to the complement of a block region precisely when
the blocks containing both endpoints are disjoint from that region.  This is
strictly stronger than merely saying that the whole two-block carrier is not a
subset of the region.  The latter would incorrectly retain bonds crossing the
boundary of `Y₀`.

The terminal endpoints identify membership in the physical `P` powerset and
prove, for every selected bond, the three source clauses: ambient membership,
disjointness from `Y₀`, and exclusion from the distinguished family.
-/

namespace YangMills.RG

open Finset

/-- Physical bonds whose two endpoint blocks are disjoint from `Y₀`. -/
noncomputable def cmp116BondsOutsideBlockRegion {d M N' : ℕ}
    [NeZero M] [NeZero N'] (Y0 : Finset (FinBox d N')) :
    Finset (PhysicalBond d (M * N')) :=
  by
    classical
    exact Finset.univ.filter fun e => Disjoint (cmp116BondBlocks e) Y0

@[simp] theorem mem_cmp116BondsOutsideBlockRegion_iff {d M N' : ℕ}
    [NeZero M] [NeZero N'] {Y0 : Finset (FinBox d N')}
    {e : PhysicalBond d (M * N')} :
    e ∈ cmp116BondsOutsideBlockRegion Y0 ↔
      Disjoint (cmp116BondBlocks e) Y0 := by
  classical
  simp [cmp116BondsOutsideBlockRegion]

/-- Endpoint form of complete physical-bond exclusion from `Y₀`. -/
theorem mem_cmp116BondsOutsideBlockRegion_iff_endpoints {d M N' : ℕ}
    [NeZero M] [NeZero N'] {Y0 : Finset (FinBox d N')}
    {e : PhysicalBond d (M * N')} :
    e ∈ cmp116BondsOutsideBlockRegion Y0 ↔
      cmp116BondSourceBlock e ∉ Y0 ∧ cmp116BondTargetBlock e ∉ Y0 := by
  classical
  rw [mem_cmp116BondsOutsideBlockRegion_iff]
  simp [Finset.disjoint_left, cmp116BondBlocks]

/-- Literal physical carrier `Y₀^{c,*}` relative to an ambient bond family,
with the distinguished bonds removed. -/
noncomputable def cmp116Eq23PhysicalBondOutsideCarrier {d M N' : ℕ}
    [NeZero M] [NeZero N']
    (ambient distinguished : Finset (PhysicalBond d (M * N')))
    (D : Finset (Finset (FinBox d N'))) :
    Finset (PhysicalBond d (M * N')) :=
  (ambient ∩ cmp116BondsOutsideBlockRegion (cmp116Eq23Y0 D)) \ distinguished

@[simp] theorem mem_cmp116Eq23PhysicalBondOutsideCarrier_iff {d M N' : ℕ}
    [NeZero M] [NeZero N']
    {ambient distinguished : Finset (PhysicalBond d (M * N'))}
    {D : Finset (Finset (FinBox d N'))}
    {e : PhysicalBond d (M * N')} :
    e ∈ cmp116Eq23PhysicalBondOutsideCarrier ambient distinguished D ↔
      e ∈ ambient ∧
      Disjoint (cmp116BondBlocks e) (cmp116Eq23Y0 D) ∧
      e ∉ distinguished := by
  classical
  simp [cmp116Eq23PhysicalBondOutsideCarrier, and_assoc]

/-- The source-shaped physical family of all finite choices
`P ⊆ Y₀^{c,*}`. -/
noncomputable def cmp116Eq23PhysicalBondPIndex {d M N' : ℕ}
    [NeZero M] [NeZero N']
    (ambient distinguished : Finset (PhysicalBond d (M * N')))
    (D : Finset (Finset (FinBox d N'))) :
    Finset (Finset (PhysicalBond d (M * N'))) :=
  (cmp116Eq23PhysicalBondOutsideCarrier ambient distinguished D).powerset

@[simp] theorem mem_cmp116Eq23PhysicalBondPIndex_iff {d M N' : ℕ}
    [NeZero M] [NeZero N']
    {ambient distinguished : Finset (PhysicalBond d (M * N'))}
    {D : Finset (Finset (FinBox d N'))}
    {P : Finset (PhysicalBond d (M * N'))} :
    P ∈ cmp116Eq23PhysicalBondPIndex ambient distinguished D ↔
      P ⊆ cmp116Eq23PhysicalBondOutsideCarrier ambient distinguished D := by
  classical
  simp [cmp116Eq23PhysicalBondPIndex]

/-- Every bond selected by the physical `P` index lies in the declared
ambient bond family. -/
theorem cmp116Eq23PhysicalBondPIndex_mem_ambient {d M N' : ℕ}
    [NeZero M] [NeZero N']
    {ambient distinguished : Finset (PhysicalBond d (M * N'))}
    {D : Finset (Finset (FinBox d N'))}
    {P : Finset (PhysicalBond d (M * N'))}
    (hP : P ∈ cmp116Eq23PhysicalBondPIndex ambient distinguished D)
    {e : PhysicalBond d (M * N')} (heP : e ∈ P) :
    e ∈ ambient := by
  have heCarrier := (mem_cmp116Eq23PhysicalBondPIndex_iff.mp hP) heP
  exact (mem_cmp116Eq23PhysicalBondOutsideCarrier_iff.mp heCarrier).1

/-- Every selected bond is completely outside `Y₀`, endpoint by endpoint. -/
theorem cmp116Eq23PhysicalBondPIndex_disjoint_Y0 {d M N' : ℕ}
    [NeZero M] [NeZero N']
    {ambient distinguished : Finset (PhysicalBond d (M * N'))}
    {D : Finset (Finset (FinBox d N'))}
    {P : Finset (PhysicalBond d (M * N'))}
    (hP : P ∈ cmp116Eq23PhysicalBondPIndex ambient distinguished D)
    {e : PhysicalBond d (M * N')} (heP : e ∈ P) :
    Disjoint (cmp116BondBlocks e) (cmp116Eq23Y0 D) := by
  have heCarrier := (mem_cmp116Eq23PhysicalBondPIndex_iff.mp hP) heP
  exact (mem_cmp116Eq23PhysicalBondOutsideCarrier_iff.mp heCarrier).2.1

/-- No selected bond is one of the distinguished `b₀(c)` bonds. -/
theorem cmp116Eq23PhysicalBondPIndex_not_distinguished {d M N' : ℕ}
    [NeZero M] [NeZero N']
    {ambient distinguished : Finset (PhysicalBond d (M * N'))}
    {D : Finset (Finset (FinBox d N'))}
    {P : Finset (PhysicalBond d (M * N'))}
    (hP : P ∈ cmp116Eq23PhysicalBondPIndex ambient distinguished D)
    {e : PhysicalBond d (M * N')} (heP : e ∈ P) :
    e ∉ distinguished := by
  have heCarrier := (mem_cmp116Eq23PhysicalBondPIndex_iff.mp hP) heP
  exact (mem_cmp116Eq23PhysicalBondOutsideCarrier_iff.mp heCarrier).2.2

/-- Complete source membership package for one selected physical bond. -/
theorem cmp116Eq23PhysicalBondPIndex_bond_iff {d M N' : ℕ}
    [NeZero M] [NeZero N']
    {ambient distinguished : Finset (PhysicalBond d (M * N'))}
    {D : Finset (Finset (FinBox d N'))}
    {P : Finset (PhysicalBond d (M * N'))}
    (hP : P ∈ cmp116Eq23PhysicalBondPIndex ambient distinguished D)
    {e : PhysicalBond d (M * N')} (heP : e ∈ P) :
    e ∈ ambient ∧
      cmp116BondSourceBlock e ∉ cmp116Eq23Y0 D ∧
      cmp116BondTargetBlock e ∉ cmp116Eq23Y0 D ∧
      e ∉ distinguished := by
  have hdisjoint := cmp116Eq23PhysicalBondPIndex_disjoint_Y0 hP heP
  have hendpoints :
      cmp116BondSourceBlock e ∉ cmp116Eq23Y0 D ∧
        cmp116BondTargetBlock e ∉ cmp116Eq23Y0 D := by
    simpa [Finset.disjoint_left, cmp116BondBlocks] using hdisjoint
  exact ⟨cmp116Eq23PhysicalBondPIndex_mem_ambient hP heP,
    hendpoints.1, hendpoints.2,
    cmp116Eq23PhysicalBondPIndex_not_distinguished hP heP⟩

end YangMills.RG
