/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4FaaDiBrunoPhysicalDomainExpansion
import YangMills.RG.BalabanCMP116Eq222CutoffSupNormTransport

/-!
# Physical cutoff carrier of the connected equation-(80) domains

The connected-domain decomposition of the literal equation-(80) potential is
indexed by coarse block carriers containing the common `Pi^4` anchor.  This
file converts each such label into the source `CMP116LocalizationDomain`,
takes its bilateral physical bond support, and defines the small-field carrier
`Y0` as the literal union of the selected domain supports.

Consequently every selected equation-(80) domain has bond support contained
in `Y0`, and nonvanishing of the CMP116 cutoff places the field projected to
that support inside the source sup-norm ball.  This is a geometric/norm
dictionary.  It does not yet prove that the connected activity is invariant
under replacing the ambient field by this projection, nor equation (1.36).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No placeholders or
local axioms.
-/

namespace YangMills.RG

noncomputable section

/-- The finite type of connected physical block labels occurring in the
equation-(80) Faa di Bruno decomposition at one `Pi^4` anchor. -/
abbrev CMP102Eq80SourcePi4PhysicalDomainLabel
    {Q : ℕ} [NeZero Q] (anchor : FinBox 4 Q) :=
  ↥(cmp102Eq80SourcePi4FaaDiBrunoPhysicalDomainLabels anchor)

/-- Membership in the finite physical-label type exposes the printed anchor
and face-connectivity conditions. -/
theorem CMP102Eq80SourcePi4PhysicalDomainLabel.properties
    {Q : ℕ} [NeZero Q] (anchor : FinBox 4 Q)
    (W : CMP102Eq80SourcePi4PhysicalDomainLabel anchor) :
    cmp102Eq80SourcePi4AnchorCarrier anchor ⊆ W.1 ∧
      walkConnected (cmp116CoarseFaceAdj 4 (2 * Q)) W.1 := by
  classical
  have hmem :
      W.1 ∈ cmp102Eq80SourcePi4FaaDiBrunoPhysicalDomainLabels anchor :=
    W.2
  change W.1 ∈
    (Finset.univ.filter fun W =>
      cmp102Eq80SourcePi4AnchorCarrier anchor ⊆ W ∧
        walkConnected (cmp116CoarseFaceAdj 4 (2 * Q)) W) at hmem
  exact (Finset.mem_filter.mp hmem).2

/-- A connected equation-(80) block label, interpreted as the literal
CMP116 localization domain at fine scale `M`. -/
noncomputable def cmp102Eq80SourcePi4LocalizationDomain
    {M Q : ℕ} [NeZero Q]
    (anchor : FinBox 4 Q)
    (W : CMP102Eq80SourcePi4PhysicalDomainLabel anchor) :
    CMP116LocalizationDomain M (2 * Q) where
  blocks := W.1
  nonempty := by
    have hproperties := W.properties anchor
    obtain ⟨block, hblock⟩ :=
      cmp102Eq80SourcePi4AnchorCarrier_nonempty anchor
    exact ⟨block, hproperties.1 hblock⟩
  connected := by
    have hproperties := W.properties anchor
    exact hproperties.2

/-- The finite family of bilateral physical bond supports of the selected
equation-(80) domains. -/
noncomputable def cmp102Eq80SourcePi4BondDomainFamily
    {M Q : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor)) :
    Finset (Finset (PhysicalBond 4 (M * (2 * Q)))) :=
  D.image fun W =>
    (cmp102Eq80SourcePi4LocalizationDomain
      (M := M) anchor W).bondSupport

/-- The source small-field carrier is the literal union of the selected
physical domain bond supports. -/
noncomputable def cmp102Eq80SourcePi4PhysicalY0
    {M Q : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor)) :
    Finset (PhysicalBond 4 (M * (2 * Q))) :=
  cmp116Eq23Y0 (cmp102Eq80SourcePi4BondDomainFamily (M := M) anchor D)

/-- Every selected equation-(80) domain reads a bilateral physical bond
carrier contained in the literal source `Y0`. -/
theorem cmp102Eq80SourcePi4LocalizationDomain_bondSupport_subset_physicalY0
    {M Q : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (W : CMP102Eq80SourcePi4PhysicalDomainLabel anchor)
    (hW : W ∈ D) :
    (cmp102Eq80SourcePi4LocalizationDomain
        (M := M) anchor W).bondSupport ⊆
      cmp102Eq80SourcePi4PhysicalY0 (M := M) anchor D := by
  intro bond hbond
  apply mem_cmp116Eq23Y0_iff.mpr
  refine ⟨
    (cmp102Eq80SourcePi4LocalizationDomain
      (M := M) anchor W).bondSupport, ?_, hbond⟩
  exact Finset.mem_image.mpr ⟨W, hW, rfl⟩

/-- On nonzero cutoff support, the physical field localized to any selected
equation-(80) domain lies in the source-facing small-field sup-norm ball. -/
theorem cmp98SourceFieldSupNorm_eq80DomainProjection_le_threshold_of_cutoffFactor_ne_zero
    {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (W : CMP102Eq80SourcePi4PhysicalDomainLabel anchor)
    (hW : W ∈ D)
    (P : Finset (PhysicalBond 4 (M * (2 * Q))))
    (threshold : ℝ)
    (b : CMP116Eq214GaussianCoordinate
      (PhysicalBond 4 (M * (2 * Q))) (Nc ^ 2 - 1))
    (hthreshold : 0 ≤ threshold)
    (hcutoff :
      (-1 : ℂ) ^ P.card *
          cmp116SmallFieldCutoff
            (cmp102Eq80SourcePi4PhysicalY0 (M := M) anchor D)
            threshold (cmp116SourcePhysicalCoordinateCochain b) *
          cmp116LargeFieldCutoff P threshold
            (cmp116SourcePhysicalCoordinateCochain b) ≠ 0) :
    cmp98SourceFieldSupNorm
        (physicalBondProjection
          (cmp102Eq80SourcePi4LocalizationDomain
            (M := M) anchor W).bondSupport
          (cmp116SourcePhysicalCoordinateCochain b)) ≤ threshold := by
  exact
    cmp98SourceFieldSupNorm_physicalBondProjection_le_threshold_of_cutoffFactor_ne_zero
      (cmp102Eq80SourcePi4PhysicalY0 (M := M) anchor D)
      P
      (cmp102Eq80SourcePi4LocalizationDomain
        (M := M) anchor W).bondSupport
      threshold b hthreshold
      (cmp102Eq80SourcePi4LocalizationDomain_bondSupport_subset_physicalY0
        anchor D W hW)
      hcutoff

end

end YangMills.RG
