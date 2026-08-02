/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourceRestrictedPhysicalOuterBoundary
import YangMills.RG.BalabanCMP116Eq223PhysicalLocalizationProjector

/-!
# Source coordinates transported to the physical bond basis

The equation-(2.26) geometry is indexed by CMP116 cubes, whereas the literal
source Gaussian is indexed by physical bonds and Lie coordinates.  This file
performs that transport through the certified dictionary equivalence.  It
does not identify cubes with bonds.
-/

namespace YangMills.RG

noncomputable section

/-- The physical bond--Lie carrier corresponding exactly to the CMP116
localized coordinate carrier. -/
noncomputable def cmp116SourcePhysicalLocalizedCoordinates
    {d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (Z0 : Finset (FinBox d N')) :
    Finset (PhysicalGaugeCoordIndex d (M * N') Nc) :=
  (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0).map
    Dict.coordEquiv.toEmbedding

@[simp]
theorem mem_cmp116SourcePhysicalLocalizedCoordinates_iff
    {d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (Z0 : Finset (FinBox d N'))
    (ba : PhysicalGaugeCoordIndex d (M * N') Nc) :
    ba ∈ cmp116SourcePhysicalLocalizedCoordinates Dict Z0 ↔
      cmp116BondInterior Z0 ba.1 := by
  classical
  constructor
  · intro hba
    rw [cmp116SourcePhysicalLocalizedCoordinates, Finset.mem_map] at hba
    obtain ⟨qa, hqa, hqa_eq⟩ := hba
    subst ba
    exact
      (Dict.mem_cmp116Eq223PhysicalLocalizedCoordinates_iff Z0 qa).mp hqa
  · intro hba
    let qa := Dict.coordEquiv.symm ba
    have hqa :
        qa ∈ Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0 := by
      rw [Dict.mem_cmp116Eq223PhysicalLocalizedCoordinates_iff]
      simpa [qa] using hba
    rw [cmp116SourcePhysicalLocalizedCoordinates, Finset.mem_map]
    exact ⟨qa, hqa, by simp [qa]⟩

/-- Transport through the coordinate equivalence preserves the localized
carrier cardinality exactly. -/
theorem card_cmp116SourcePhysicalLocalizedCoordinates
    {d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (Z0 : Finset (FinBox d N')) :
    (cmp116SourcePhysicalLocalizedCoordinates Dict Z0).card =
      (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0).card := by
  classical
  exact Finset.card_map _

/-- The physical source carrier inherits the explicit volume-uniform
cardinality bound from the CMP116 dictionary. -/
theorem card_cmp116SourcePhysicalLocalizedCoordinates_le
    {d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (Z0 : Finset (FinBox d N')) :
    (cmp116SourcePhysicalLocalizedCoordinates Dict Z0).card ≤
      ((Z0.card * M ^ d) * d) * (Nc ^ 2 - 1) := by
  rw [card_cmp116SourcePhysicalLocalizedCoordinates]
  exact Dict.card_cmp116Eq223PhysicalLocalizedCoordinates_le Z0

/-- The empty block region has no localized physical coordinate.  This is a
structural fact about the literal two-endpoint interior, not a cardinality
estimate. -/
@[simp]
theorem cmp116SourcePhysicalLocalizedCoordinates_empty
    {d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim) :
    cmp116SourcePhysicalLocalizedCoordinates Dict
        (∅ : Finset (FinBox d N')) = ∅ := by
  classical
  ext ba
  constructor
  · intro hba
    have hinterior : cmp116BondInterior (∅ : Finset (FinBox d N')) ba.1 :=
      (mem_cmp116SourcePhysicalLocalizedCoordinates_iff Dict ∅ ba).mp hba
    have hsource := hinterior.1.1
    rw [mem_cmp116RegionSites_iff] at hsource
    simpa using hsource
  · intro hba
    simp at hba

/-- A cube carrier is converted to its literal physical bond carrier by the
site map; no cube is treated definitionally as a bond. -/
noncomputable def cmp116SourcePhysicalBondsOfCells
    {d N Nc L lieDim : ℕ} [NeZero N] [NeZero L]
    (Dict : PhysicalGaugeCMP116Dictionary d N Nc d L lieDim)
    (X : Finset (Cube d L)) :
    Finset (PhysicalBond d N) :=
  Dict.physicalBondsOfCells X

@[simp]
theorem mem_cmp116SourcePhysicalBondsOfCells_iff
    {d N Nc L lieDim : ℕ} [NeZero N] [NeZero L]
    (Dict : PhysicalGaugeCMP116Dictionary d N Nc d L lieDim)
    (X : Finset (Cube d L)) (b : PhysicalBond d N) :
    b ∈ cmp116SourcePhysicalBondsOfCells Dict X ↔
      Dict.siteMap.bondToCube b ∈ X := by
  exact Dict.mem_physicalBondsOfCells X b

end

end YangMills.RG
