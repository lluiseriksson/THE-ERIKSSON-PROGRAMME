/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214Interior

/-!
# CMP116 equation (2.14): the least interior-compatible localization core

This module constructs, rather than merely postulates, the smallest block
carrier forced by `(D,P)` and by the requirement that every large-field bond
of `P` lie in the discrete interior.

For a physical site, its interior stencil is the block containing it together
with the blocks containing all forward and backward nearest neighbours.  For a
bond, the required carrier is the union of the stencils of both endpoints.
Adjoining these carriers to the `(D,P)` seed gives `cmp116LocalizationCore`.

The terminal equivalence says literally that this core is contained in `Z₀`
if and only if `Z₀` contains the seed and every bond in `P` is interior.  Thus
the core is the exact least solution of the incidence/interior constraints.

Honest scope: CMP116's localization *domain* may additionally impose a
connected-domain convention.  The core constructed here need not be connected
when the physical input has separated components; no arbitrary connecting path
is selected.  Its face components, and any source-specific connected envelope,
remain separate geometric data.
-/

namespace YangMills.RG

open Finset

/-- Blocks needed to make a physical site an interior site. -/
noncomputable def cmp116SiteInteriorBlocks {d M N' : ℕ}
    [NeZero M] [NeZero N'] (x : FinBox d (M * N')) :
    Finset (FinBox d N') :=
  insert (blockSite M N' x)
    ((Finset.univ : Finset (Fin d)).biUnion fun i =>
      {blockSite M N' (FinBox.shift x i),
       blockSite M N' (FinBox.shiftBack x i)})

@[simp] theorem mem_cmp116SiteInteriorBlocks_iff {d M N' : ℕ}
    [NeZero M] [NeZero N'] {x : FinBox d (M * N')} {c : FinBox d N'} :
    c ∈ cmp116SiteInteriorBlocks x ↔
      c = blockSite M N' x ∨
      ∃ i : Fin d,
        c = blockSite M N' (FinBox.shift x i) ∨
        c = blockSite M N' (FinBox.shiftBack x i) := by
  classical
  simp [cmp116SiteInteriorBlocks]

/-- A site is interior exactly when its complete stencil is contained in the
block region. -/
theorem cmp116SiteInterior_iff_blocks_subset {d M N' : ℕ}
    [NeZero M] [NeZero N'] {Z0 : Finset (FinBox d N')}
    {x : FinBox d (M * N')} :
    cmp116SiteInterior Z0 x ↔ cmp116SiteInteriorBlocks x ⊆ Z0 := by
  classical
  constructor
  · intro hx c hc
    rw [mem_cmp116SiteInteriorBlocks_iff] at hc
    rcases hc with rfl | ⟨i, rfl | rfl⟩
    · exact mem_cmp116RegionSites_iff.mp hx.1
    · exact mem_cmp116RegionSites_iff.mp (hx.2 i).1
    · exact mem_cmp116RegionSites_iff.mp (hx.2 i).2
  · intro h
    constructor
    · exact mem_cmp116RegionSites_iff.mpr
        (h (by simp [cmp116SiteInteriorBlocks]))
    · intro i
      constructor
      · exact mem_cmp116RegionSites_iff.mpr
          (h (mem_cmp116SiteInteriorBlocks_iff.mpr (Or.inr ⟨i, Or.inl rfl⟩)))
      · exact mem_cmp116RegionSites_iff.mpr
          (h (mem_cmp116SiteInteriorBlocks_iff.mpr (Or.inr ⟨i, Or.inr rfl⟩)))

/-- Blocks needed to make both physical endpoints of a bond interior. -/
noncomputable def cmp116BondInteriorBlocks {d M N' : ℕ}
    [NeZero M] [NeZero N'] (e : PhysicalBond d (M * N')) :
    Finset (FinBox d N') :=
  cmp116SiteInteriorBlocks (cmp116BondSource e) ∪
    cmp116SiteInteriorBlocks (cmp116BondTarget e)

@[simp] theorem mem_cmp116BondInteriorBlocks_iff {d M N' : ℕ}
    [NeZero M] [NeZero N'] {e : PhysicalBond d (M * N')}
    {c : FinBox d N'} :
    c ∈ cmp116BondInteriorBlocks e ↔
      c ∈ cmp116SiteInteriorBlocks (cmp116BondSource e) ∨
      c ∈ cmp116SiteInteriorBlocks (cmp116BondTarget e) := by
  simp [cmp116BondInteriorBlocks]

/-- A bond is interior exactly when its complete two-endpoint stencil is
contained in the block region. -/
theorem cmp116BondInterior_iff_blocks_subset {d M N' : ℕ}
    [NeZero M] [NeZero N'] {Z0 : Finset (FinBox d N')}
    {e : PhysicalBond d (M * N')} :
    cmp116BondInterior Z0 e ↔ cmp116BondInteriorBlocks e ⊆ Z0 := by
  classical
  rw [cmp116BondInterior, cmp116BondInteriorBlocks, union_subset_iff]
  exact and_congr cmp116SiteInterior_iff_blocks_subset
    cmp116SiteInterior_iff_blocks_subset

/-- The exact finite block core forced by `(D,P)` and bond interiority. -/
noncomputable def cmp116LocalizationCore {d M N' : ℕ}
    [NeZero M] [NeZero N']
    (D : Finset (Finset (FinBox d N')))
    (P : Finset (PhysicalBond d (M * N'))) : Finset (FinBox d N') :=
  cmp116LocalizationSeed D P ∪ P.biUnion cmp116BondInteriorBlocks

@[simp] theorem mem_cmp116LocalizationCore_iff {d M N' : ℕ}
    [NeZero M] [NeZero N']
    {D : Finset (Finset (FinBox d N'))}
    {P : Finset (PhysicalBond d (M * N'))} {c : FinBox d N'} :
    c ∈ cmp116LocalizationCore D P ↔
      c ∈ cmp116LocalizationSeed D P ∨
      ∃ e ∈ P, c ∈ cmp116BondInteriorBlocks e := by
  classical
  simp [cmp116LocalizationCore]

/-- Predicate isolated from the construction: `Z₀` contains the physical seed
and makes every large-field bond interior. -/
def CMP116LocalizationAdmissible {d M N' : ℕ}
    [NeZero M] [NeZero N']
    (D : Finset (Finset (FinBox d N')))
    (P : Finset (PhysicalBond d (M * N')))
    (Z0 : Finset (FinBox d N')) : Prop :=
  cmp116LocalizationSeed D P ⊆ Z0 ∧
    ∀ e ∈ P, cmp116BondInterior Z0 e

/-- The constructed core contains the original `(D,P)` seed. -/
theorem cmp116LocalizationSeed_subset_core {d M N' : ℕ}
    [NeZero M] [NeZero N']
    (D : Finset (Finset (FinBox d N')))
    (P : Finset (PhysicalBond d (M * N'))) :
    cmp116LocalizationSeed D P ⊆ cmp116LocalizationCore D P := by
  classical
  exact Finset.subset_union_left

/-- Every selected large-field bond is interior to the constructed core. -/
theorem cmp116BondInterior_localizationCore {d M N' : ℕ}
    [NeZero M] [NeZero N']
    (D : Finset (Finset (FinBox d N')))
    {P : Finset (PhysicalBond d (M * N'))}
    {e : PhysicalBond d (M * N')} (heP : e ∈ P) :
    cmp116BondInterior (cmp116LocalizationCore D P) e := by
  classical
  rw [cmp116BondInterior_iff_blocks_subset]
  intro c hc
  exact mem_cmp116LocalizationCore_iff.mpr (Or.inr ⟨e, heP, hc⟩)

/-- The core itself satisfies all incidence/interior constraints. -/
theorem cmp116LocalizationCore_admissible {d M N' : ℕ}
    [NeZero M] [NeZero N']
    (D : Finset (Finset (FinBox d N')))
    (P : Finset (PhysicalBond d (M * N'))) :
    CMP116LocalizationAdmissible D P (cmp116LocalizationCore D P) := by
  exact ⟨cmp116LocalizationSeed_subset_core D P,
    fun _ he => cmp116BondInterior_localizationCore D he⟩

/-- Exact minimality: a block carrier contains the constructed core precisely
when it satisfies all physical seed and interior constraints. -/
theorem cmp116LocalizationCore_subset_iff_admissible {d M N' : ℕ}
    [NeZero M] [NeZero N']
    (D : Finset (Finset (FinBox d N')))
    (P : Finset (PhysicalBond d (M * N')))
    (Z0 : Finset (FinBox d N')) :
    cmp116LocalizationCore D P ⊆ Z0 ↔
      CMP116LocalizationAdmissible D P Z0 := by
  classical
  constructor
  · intro h
    constructor
    · exact fun c hc => h (cmp116LocalizationSeed_subset_core D P hc)
    · intro e heP
      rw [cmp116BondInterior_iff_blocks_subset]
      intro c hc
      exact h (mem_cmp116LocalizationCore_iff.mpr (Or.inr ⟨e, heP, hc⟩))
  · rintro ⟨hseed, hP⟩ c hc
    rw [mem_cmp116LocalizationCore_iff] at hc
    rcases hc with hc | ⟨e, heP, hc⟩
    · exact hseed hc
    · exact (cmp116BondInterior_iff_blocks_subset.mp (hP e heP)) hc

/-- Any admissible localization region contains the canonical core. -/
theorem cmp116LocalizationCore_minimal {d M N' : ℕ}
    [NeZero M] [NeZero N']
    {D : Finset (Finset (FinBox d N'))}
    {P : Finset (PhysicalBond d (M * N'))}
    {Z0 : Finset (FinBox d N')}
    (hZ0 : CMP116LocalizationAdmissible D P Z0) :
    cmp116LocalizationCore D P ⊆ Z0 :=
  (cmp116LocalizationCore_subset_iff_admissible D P Z0).mpr hZ0

end YangMills.RG
