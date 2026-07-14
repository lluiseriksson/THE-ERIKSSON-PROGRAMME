/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214Incidence

/-!
# CMP116 equation (2.14): discrete interior and boundary of `Z₀`

CMP116 chooses the smallest localization region containing `Y₀` and the
large-field bonds `P`, with every bond of `P` contained in the interior and
disjoint from the boundary.  This module gives those words a concrete finite
periodic-lattice meaning.

A block region `Z₀` induces the union of its physical `M`-blocks.  A physical
site is interior when it and all of its forward and backward nearest neighbours
belong to that union.  Boundary sites are precisely the remaining sites of the
union.  A bond is interior when both of its endpoints are interior sites.

This definition uses both orientations around every site and is therefore not
the earlier one-endpoint encoding which the Eq. (2.31) source audit rejected.
It also keeps the within-block physical coordinates until after the boundary
test.  The next module may consequently form the least admissible block region
without choosing an arbitrary connecting path.
-/

namespace YangMills.RG

open Finset

/-- Physical sites covered by a family of `M`-blocks. -/
noncomputable def cmp116RegionSites {d M N' : ℕ} [NeZero M]
    (Z0 : Finset (FinBox d N')) : Finset (FinBox d (M * N')) :=
  Z0.biUnion (blockOf M N')

@[simp] theorem mem_cmp116RegionSites_iff {d M N' : ℕ} [NeZero M]
    {Z0 : Finset (FinBox d N')} {x : FinBox d (M * N')} :
    x ∈ cmp116RegionSites Z0 ↔ blockSite M N' x ∈ Z0 := by
  classical
  simp [cmp116RegionSites, mem_blockOf]

/-- A site lies in the discrete interior when the site and all `2d` nearest
neighbours lie in the physical region induced by `Z₀`. -/
def cmp116SiteInterior {d M N' : ℕ} [NeZero M] [NeZero N']
    (Z0 : Finset (FinBox d N')) (x : FinBox d (M * N')) : Prop :=
  x ∈ cmp116RegionSites Z0 ∧
    ∀ i : Fin d,
      FinBox.shift x i ∈ cmp116RegionSites Z0 ∧
      FinBox.shiftBack x i ∈ cmp116RegionSites Z0

/-- Finite carrier of the interior physical sites. -/
noncomputable def cmp116InteriorSites {d M N' : ℕ} [NeZero M] [NeZero N']
    (Z0 : Finset (FinBox d N')) : Finset (FinBox d (M * N')) :=
  by
    classical
    exact (cmp116RegionSites Z0).filter (cmp116SiteInterior Z0)

/-- Finite carrier of the boundary physical sites. -/
noncomputable def cmp116BoundarySites {d M N' : ℕ} [NeZero M] [NeZero N']
    (Z0 : Finset (FinBox d N')) : Finset (FinBox d (M * N')) :=
  by
    classical
    exact (cmp116RegionSites Z0).filter fun x => ¬cmp116SiteInterior Z0 x

@[simp] theorem mem_cmp116InteriorSites_iff {d M N' : ℕ}
    [NeZero M] [NeZero N']
    {Z0 : Finset (FinBox d N')} {x : FinBox d (M * N')} :
    x ∈ cmp116InteriorSites Z0 ↔ cmp116SiteInterior Z0 x := by
  classical
  constructor
  · exact fun hx => (Finset.mem_filter.mp hx).2
  · intro hx
    exact Finset.mem_filter.mpr ⟨hx.1, hx⟩

@[simp] theorem mem_cmp116BoundarySites_iff {d M N' : ℕ}
    [NeZero M] [NeZero N']
    {Z0 : Finset (FinBox d N')} {x : FinBox d (M * N')} :
    x ∈ cmp116BoundarySites Z0 ↔
      x ∈ cmp116RegionSites Z0 ∧ ¬cmp116SiteInterior Z0 x := by
  classical
  exact Finset.mem_filter

theorem cmp116InteriorSites_union_boundarySites {d M N' : ℕ}
    [NeZero M] [NeZero N'] (Z0 : Finset (FinBox d N')) :
    cmp116InteriorSites (d := d) (M := M) (N' := N') Z0 ∪
        cmp116BoundarySites (d := d) (M := M) (N' := N') Z0 =
      cmp116RegionSites (d := d) (M := M) (N' := N') Z0 := by
  classical
  ext x
  by_cases hx : cmp116SiteInterior Z0 x
  · simp [hx, hx.1]
  · simp [hx]

theorem cmp116InteriorSites_disjoint_boundarySites {d M N' : ℕ}
    [NeZero M] [NeZero N'] (Z0 : Finset (FinBox d N')) :
    Disjoint
      (cmp116InteriorSites (d := d) (M := M) (N' := N') Z0)
      (cmp116BoundarySites (d := d) (M := M) (N' := N') Z0) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro x hxInterior hxBoundary
  exact (mem_cmp116BoundarySites_iff.mp hxBoundary).2
    (mem_cmp116InteriorSites_iff.mp hxInterior)

/-- The two physical endpoints of a positively oriented bond. -/
def cmp116BondEndpoints {d N : ℕ} [NeZero N]
    (e : PhysicalBond d N) : Finset (FinBox d N) :=
  {cmp116BondSource e, cmp116BondTarget e}

@[simp] theorem mem_cmp116BondEndpoints_iff {d N : ℕ} [NeZero N]
    {e : PhysicalBond d N} {x : FinBox d N} :
    x ∈ cmp116BondEndpoints e ↔
      x = cmp116BondSource e ∨ x = cmp116BondTarget e := by
  simp [cmp116BondEndpoints]

/-- Source-faithful discrete interpretation of a bond lying in the interior of
the block region `Z₀`. -/
def cmp116BondInterior {d M N' : ℕ} [NeZero M] [NeZero N']
    (Z0 : Finset (FinBox d N')) (e : PhysicalBond d (M * N')) : Prop :=
  cmp116SiteInterior Z0 (cmp116BondSource e) ∧
    cmp116SiteInterior Z0 (cmp116BondTarget e)

theorem cmp116BondInterior_iff_endpoints_subset {d M N' : ℕ}
    [NeZero M] [NeZero N']
    {Z0 : Finset (FinBox d N')} {e : PhysicalBond d (M * N')} :
    cmp116BondInterior Z0 e ↔
      cmp116BondEndpoints e ⊆ cmp116InteriorSites Z0 := by
  classical
  constructor
  · intro he x hx
    rw [mem_cmp116BondEndpoints_iff] at hx
    rcases hx with rfl | rfl
    · exact mem_cmp116InteriorSites_iff.mpr he.1
    · exact mem_cmp116InteriorSites_iff.mpr he.2
  · intro h
    constructor
    · exact mem_cmp116InteriorSites_iff.mp
        (h (by simp [cmp116BondEndpoints]))
    · exact mem_cmp116InteriorSites_iff.mp
        (h (by simp [cmp116BondEndpoints]))

/-- An interior bond can hit only blocks belonging to `Z₀`. -/
theorem cmp116BondBlocks_subset_of_interior {d M N' : ℕ}
    [NeZero M] [NeZero N']
    {Z0 : Finset (FinBox d N')} {e : PhysicalBond d (M * N')}
    (he : cmp116BondInterior Z0 e) :
    cmp116BondBlocks e ⊆ Z0 := by
  intro y hy
  rw [mem_cmp116BondBlocks_iff] at hy
  rcases hy with rfl | rfl
  · exact mem_cmp116RegionSites_iff.mp he.1.1
  · exact mem_cmp116RegionSites_iff.mp he.2.1

/-- The endpoints of an interior bond are disjoint from the physical boundary
of `Z₀`. -/
theorem cmp116BondEndpoints_disjoint_boundary_of_interior {d M N' : ℕ}
    [NeZero M] [NeZero N']
    {Z0 : Finset (FinBox d N')} {e : PhysicalBond d (M * N')}
    (he : cmp116BondInterior Z0 e) :
    Disjoint (cmp116BondEndpoints e) (cmp116BoundarySites Z0) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro x hxEndpoint hxBoundary
  have hxInterior : x ∈ cmp116InteriorSites Z0 :=
    (cmp116BondInterior_iff_endpoints_subset.mp he) hxEndpoint
  exact (mem_cmp116BoundarySites_iff.mp hxBoundary).2
    (mem_cmp116InteriorSites_iff.mp hxInterior)

@[simp] theorem cmp116RegionSites_univ {d M N' : ℕ} [NeZero M] :
    cmp116RegionSites (d := d) (M := M) (N' := N')
      (Finset.univ : Finset (FinBox d N')) = Finset.univ := by
  classical
  ext x
  simp

theorem cmp116SiteInterior_univ {d M N' : ℕ} [NeZero M] [NeZero N']
    (x : FinBox d (M * N')) :
    cmp116SiteInterior (d := d) (M := M) (N' := N')
      (Finset.univ : Finset (FinBox d N')) x := by
  simp [cmp116SiteInterior]

theorem cmp116BondInterior_univ {d M N' : ℕ} [NeZero M] [NeZero N']
    (e : PhysicalBond d (M * N')) :
    cmp116BondInterior (d := d) (M := M) (N' := N')
      (Finset.univ : Finset (FinBox d N')) e := by
  exact ⟨cmp116SiteInterior_univ _, cmp116SiteInterior_univ _⟩

end YangMills.RG
