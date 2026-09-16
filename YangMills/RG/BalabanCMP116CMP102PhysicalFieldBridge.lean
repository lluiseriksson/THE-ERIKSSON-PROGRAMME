/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalDomainFTCRadial
import YangMills.RG.BalabanCMP116Eq226PhysicalContourActivityBoundary

/-!
# CMP102--CMP116 physical-field bridge

CMP102 analytic producers use the finite-dimensional `PiLp 2` realization
of physical positive-bond one-cochains.  CMP116 local activities expose the
same coordinates as plain dependent functions.  This module proves that the
two carriers are canonically linearly equivalent and definitionally agree at
every physical bond.

This is the first typed bridge between the CMP102 producer lane and the
CMP116 contour consumer lane.  It does not construct a contour source record,
prove an equation-(2.26) boundary, or discharge `hprofile`.
-/

namespace YangMills.RG

noncomputable section

/-- Canonical linear equivalence from the plain CMP116 physical field to the
`PiLp 2` physical one-cochain used by CMP102. -/
noncomputable def cmp102FineFieldEquivCMP116PhysicalGaugeField
    (d L N' Nc : ℕ) [NeZero L] [NeZero N'] :
    PhysicalGaugeField d (L * N') Nc ≃ₗ[ℝ]
      FinePhysicalOneCochain d L N' Nc :=
  (WithLp.linearEquiv 2 ℝ
    (PhysicalBond d (L * N') → SUNLieCoord Nc)).symm

@[simp]
theorem cmp102FineFieldEquivCMP116PhysicalGaugeField_apply
    {d L N' Nc : ℕ} [NeZero L] [NeZero N']
    (X : PhysicalGaugeField d (L * N') Nc)
    (b : PhysicalBond d (L * N')) :
    cmp102FineFieldEquivCMP116PhysicalGaugeField d L N' Nc X b = X b :=
  rfl

@[simp]
theorem cmp102FineFieldEquivCMP116PhysicalGaugeField_symm_apply
    {d L N' Nc : ℕ} [NeZero L] [NeZero N']
    (A : FinePhysicalOneCochain d L N' Nc)
    (b : PhysicalBond d (L * N')) :
    (cmp102FineFieldEquivCMP116PhysicalGaugeField d L N' Nc).symm A b =
      A b :=
  rfl

/-- Round-trip from a CMP116 physical field through the CMP102 `PiLp`
realization. -/
@[simp]
theorem cmp116PhysicalGaugeField_roundtrip_cmp102FineField
    {d L N' Nc : ℕ} [NeZero L] [NeZero N']
    (X : PhysicalGaugeField d (L * N') Nc) :
    (cmp102FineFieldEquivCMP116PhysicalGaugeField d L N' Nc).symm
        (cmp102FineFieldEquivCMP116PhysicalGaugeField d L N' Nc X) = X :=
  (cmp102FineFieldEquivCMP116PhysicalGaugeField d L N' Nc).symm_apply_apply X

/-- Round-trip from a CMP102 `PiLp` physical field through the plain CMP116
realization. -/
@[simp]
theorem cmp102FineField_roundtrip_cmp116PhysicalGaugeField
    {d L N' Nc : ℕ} [NeZero L] [NeZero N']
    (A : FinePhysicalOneCochain d L N' Nc) :
    cmp102FineFieldEquivCMP116PhysicalGaugeField d L N' Nc
        ((cmp102FineFieldEquivCMP116PhysicalGaugeField d L N' Nc).symm A) =
      A :=
  (cmp102FineFieldEquivCMP116PhysicalGaugeField d L N' Nc).apply_symm_apply A

end

end YangMills.RG
