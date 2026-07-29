/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4CutoffCarrier
import YangMills.RG.BalabanCMP116Eq214LocalizationCore
import YangMills.RG.BalabanCMP116Eq230TreeMetric

/-!
# Canonical finite indexing of selected CMP102 source domains

The CMP116 contour record indexes localization domains by `Fin nY`, whereas
the literal CMP102 source expansion selects a finite set of connected physical
domain labels.  This file supplies the canonical equivalence between those two
finite types.

It also constructs the block region used by the centered estimate.  The bare
union of source domains is insufficient: `cmp116BondInterior` requires the
nearest neighbours of both endpoints.  We therefore use the already canonical
`cmp116LocalizationCore`, applied to the selected block domains and to the
union of the physical large-field set with all selected source bond supports.
This yields exactly the bilateral interior inclusion required by the centered
residual theorem.

No arbitrary enumeration, metric, cardinality, or padding region is accepted
as input.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No placeholders or
local axioms.
-/

namespace YangMills.RG

noncomputable section

/-- Canonical `Fin` index count of a selected finite family of physical
equation-(80) source labels. -/
abbrev CMP102Eq80SourcePi4DomainCount
    {Q : ℕ} [NeZero Q] (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor)) : ℕ :=
  D.card

/-- Canonical enumeration of the selected source domains. -/
noncomputable def cmp102Eq80SourcePi4DomainAt
    {Q : ℕ} [NeZero Q] (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (i : Fin (CMP102Eq80SourcePi4DomainCount anchor D)) :
    CMP102Eq80SourcePi4PhysicalDomainLabel anchor :=
  (D.equivFin.symm i).1

/-- Every canonical index denotes a member of the selected family. -/
theorem cmp102Eq80SourcePi4DomainAt_mem
    {Q : ℕ} [NeZero Q] (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (i : Fin (CMP102Eq80SourcePi4DomainCount anchor D)) :
    cmp102Eq80SourcePi4DomainAt anchor D i ∈ D :=
  (D.equivFin.symm i).2

/-- The canonical enumeration has no repeated selected physical labels. -/
theorem cmp102Eq80SourcePi4DomainAt_injective
    {Q : ℕ} [NeZero Q] (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor)) :
    Function.Injective (cmp102Eq80SourcePi4DomainAt anchor D) := by
  intro i j hij
  apply D.equivFin.symm.injective
  exact Subtype.ext hij

/-- The range of the canonical enumeration is exactly the selected family,
not the ambient type of every possible physical label. -/
theorem image_cmp102Eq80SourcePi4DomainAt_univ
    {Q : ℕ} [NeZero Q] (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor)) :
    Finset.image (cmp102Eq80SourcePi4DomainAt anchor D) Finset.univ = D := by
  classical
  ext W
  constructor
  · intro hW
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hW
    exact cmp102Eq80SourcePi4DomainAt_mem anchor D i
  · intro hW
    let Wsub : ↥D := ⟨W, hW⟩
    apply Finset.mem_image.mpr
    refine ⟨D.equivFin Wsub, Finset.mem_univ _, ?_⟩
    exact congrArg Subtype.val (D.equivFin.symm_apply_apply Wsub)

/-- Literal source localization domain at one canonical index. -/
noncomputable def cmp102Eq80SourcePi4IndexedLocalizationDomain
    {M Q : ℕ} [NeZero Q] (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (i : Fin (CMP102Eq80SourcePi4DomainCount anchor D)) :
    CMP116LocalizationDomain M (2 * Q) :=
  cmp102Eq80SourcePi4LocalizationDomain
    (M := M) anchor (cmp102Eq80SourcePi4DomainAt anchor D i)

/-- Source `d_k(Y)` dictionary used by the CMP116 contour ledger. -/
noncomputable def cmp102Eq80SourcePi4IndexedDomainMetric
    {M Q : ℕ} [NeZero M] [NeZero Q] (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (i : Fin (CMP102Eq80SourcePi4DomainCount anchor D)) : ℝ :=
  (cmp116CubeEdgeTreeMetric
    (cmp102Eq80SourcePi4IndexedLocalizationDomain
      (M := M) anchor D i) : ℝ)

/-- Source block cardinality used by the equation-(1.43) rate. -/
noncomputable def cmp102Eq80SourcePi4IndexedDomainCard
    {M Q : ℕ} [NeZero Q] (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (i : Fin (CMP102Eq80SourcePi4DomainCount anchor D)) : ℕ :=
  (cmp102Eq80SourcePi4IndexedLocalizationDomain
    (M := M) anchor D i).blocks.card

/-- Literal finite family of selected source block domains. -/
noncomputable def cmp102Eq80SourcePi4BlockDomainFamily
    {Q : ℕ} [NeZero Q] (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor)) :
    Finset (Finset (FinBox 4 (2 * Q))) :=
  D.image fun W => W.1

/-- Canonical centered region for the selected source family and the original
large-field bond set.  Adding all source-domain bonds to the bond argument of
the localization core supplies exactly the padding needed for bilateral
interiority. -/
noncomputable def cmp102Eq80SourcePi4CenteredRegion
    {M Q : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (P : Finset (PhysicalBond 4 (M * (2 * Q)))) :
    Finset (FinBox 4 (2 * Q)) :=
  cmp116LocalizationCore
    (cmp102Eq80SourcePi4BlockDomainFamily anchor D)
    (P ∪ cmp102Eq80SourcePi4PhysicalY0 (M := M) anchor D)

/-- Every selected literal domain bond is interior to the canonical centered
region.  This is the exact geometric premise required by the one-domain
cutoff-centered residual theorem. -/
theorem cmp102Eq80SourcePi4LocalizationDomain_bondSupport_subset_centeredRegionInterior
    {M Q : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (P : Finset (PhysicalBond 4 (M * (2 * Q))))
    (W : CMP102Eq80SourcePi4PhysicalDomainLabel anchor)
    (hW : W ∈ D) :
    (cmp102Eq80SourcePi4LocalizationDomain
        (M := M) anchor W).bondSupport ⊆
      PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds
        (cmp102Eq80SourcePi4CenteredRegion anchor D P) := by
  intro bond hbond
  rw [PhysicalGaugeCMP116Dictionary.mem_cmp116Eq223PhysicalInteriorBonds_iff]
  apply cmp116BondInterior_localizationCore
    (cmp102Eq80SourcePi4BlockDomainFamily anchor D)
  exact Finset.mem_union_right P
    (cmp102Eq80SourcePi4LocalizationDomain_bondSupport_subset_physicalY0
      anchor D W hW hbond)

/-- Indexed form of the bilateral interior inclusion. -/
theorem cmp102Eq80SourcePi4IndexedLocalizationDomain_bondSupport_subset_centeredRegionInterior
    {M Q : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (P : Finset (PhysicalBond 4 (M * (2 * Q))))
    (i : Fin (CMP102Eq80SourcePi4DomainCount anchor D)) :
    (cmp102Eq80SourcePi4IndexedLocalizationDomain
        (M := M) anchor D i).bondSupport ⊆
      PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds
        (cmp102Eq80SourcePi4CenteredRegion anchor D P) := by
  exact
    cmp102Eq80SourcePi4LocalizationDomain_bondSupport_subset_centeredRegionInterior
      anchor D P (cmp102Eq80SourcePi4DomainAt anchor D i)
      (cmp102Eq80SourcePi4DomainAt_mem anchor D i)

end

end YangMills.RG
