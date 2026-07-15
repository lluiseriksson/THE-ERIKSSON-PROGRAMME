/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214LocalizationCore
import YangMills.RG.BalabanCMP116Eq223PhysicalRootNormBridge

/-!
# CMP116 equation (2.23): the physical localization projector

The Gaussian positivity layer previously accepted an arbitrary finite set `S`
of flattened coordinates.  This module constructs that set canonically from a
physical CMP116 block region `Z0`: a scalar coordinate is selected exactly when
the physical bond assigned to it by the dictionary has both endpoints in the
discrete interior of `Z0`.

The resulting diagonal matrix is therefore the literal finite-coordinate
realization of `P_Z0`.  Its quadratic form is reindexed back to physical bonds,
and every large-field bond in an admissible `(D,P,Z0)` localization is proved to
have all of its Lie coordinates selected.

Honest scope: this identifies the carrier and projector.  It does not yet prove
the domination inequalities (2.20)--(2.22) for the physical integrand.
-/

namespace YangMills.RG

open Matrix
open scoped BigOperators

namespace PhysicalGaugeCMP116Dictionary

variable {d M N' Nc L lieDim : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
variable [NeZero Nc] [NeZero L] [NeZero lieDim]

/-- Flattened scalar coordinates whose physical bonds lie in the complete
two-endpoint interior of the block region `Z0`. -/
noncomputable def cmp116Eq223PhysicalLocalizedCoordinates
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (Z0 : Finset (FinBox d N')) :
    Finset (CMP116CoordIndex d L lieDim) := by
  classical
  exact Finset.univ.filter fun qa =>
    cmp116BondInterior Z0 (Dict.coordEquiv qa).1

@[simp] theorem mem_cmp116Eq223PhysicalLocalizedCoordinates_iff
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (Z0 : Finset (FinBox d N'))
    (qa : CMP116CoordIndex d L lieDim) :
    qa ∈ Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0 ↔
      cmp116BondInterior Z0 (Dict.coordEquiv qa).1 := by
  classical
  simp [cmp116Eq223PhysicalLocalizedCoordinates]

/-- Physical bonds whose two endpoints lie in the discrete interior of `Z0`. -/
noncomputable def cmp116Eq223PhysicalInteriorBonds
    (Z0 : Finset (FinBox d N')) : Finset (PhysicalBond d (M * N')) := by
  classical
  exact Finset.univ.filter (cmp116BondInterior Z0)

@[simp] theorem mem_cmp116Eq223PhysicalInteriorBonds_iff
    (Z0 : Finset (FinBox d N')) (e : PhysicalBond d (M * N')) :
    e ∈ cmp116Eq223PhysicalInteriorBonds Z0 ↔
      cmp116BondInterior Z0 e := by
  classical
  simp [cmp116Eq223PhysicalInteriorBonds]

/-- Exact coordinate count of the physical localization carrier.  Each
interior physical bond contributes precisely one copy of every Lie-algebra
coordinate.  This is the cardinality input needed to rewrite the outer
Gaussian factor of equation (2.25) before the geometric estimate (2.26). -/
theorem card_cmp116Eq223PhysicalLocalizedCoordinates
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (Z0 : Finset (FinBox d N')) :
    (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0).card =
      (cmp116Eq223PhysicalInteriorBonds (d := d) (M := M) (N' := N') Z0).card *
        (Nc ^ 2 - 1) := by
  classical
  let e₁ :
      {qa : CMP116CoordIndex d L lieDim //
        cmp116BondInterior (d := d) (M := M) (N' := N') Z0
          (Dict.coordEquiv qa).1} ≃
      {ba : PhysicalGaugeCoordIndex d (M * N') Nc //
        cmp116BondInterior (d := d) (M := M) (N' := N') Z0 ba.1} :=
    Dict.coordEquiv.subtypeEquiv fun _ => Iff.rfl
  let e₂ :
      {ba : PhysicalGaugeCoordIndex d (M * N') Nc //
        cmp116BondInterior (d := d) (M := M) (N' := N') Z0 ba.1} ≃
      {b : PhysicalBond d (M * N') //
        cmp116BondInterior (d := d) (M := M) (N' := N') Z0 b} ×
        Fin (Nc ^ 2 - 1) := {
    toFun ba := (⟨ba.1.1, ba.2⟩, ba.1.2)
    invFun p := ⟨(p.1.1, p.2), p.1.2⟩
    left_inv ba := by cases ba; rfl
    right_inv p := by cases p with | mk b a => cases b; rfl }
  have hcard := Fintype.card_congr (e₁.trans e₂)
  rw [Fintype.card_prod] at hcard
  rw [Fintype.card_subtype, Fintype.card_subtype] at hcard
  simpa [cmp116Eq223PhysicalLocalizedCoordinates,
    cmp116Eq223PhysicalInteriorBonds] using hcard

/-- An interior bond is determined by a region site and one of the `d`
positive lattice directions.  Consequently the number of interior bonds is
bounded linearly in the number of localization blocks. -/
theorem card_cmp116Eq223PhysicalInteriorBonds_le
    (Z0 : Finset (FinBox d N')) :
    (cmp116Eq223PhysicalInteriorBonds
      (d := d) (M := M) (N' := N') Z0).card ≤
      (Z0.card * M ^ d) * d := by
  classical
  let carrier : Finset (PhysicalBond d (M * N')) :=
    (cmp116RegionSites Z0) ×ˢ (Finset.univ : Finset (Fin d))
  have hsubset :
      cmp116Eq223PhysicalInteriorBonds
        (d := d) (M := M) (N' := N') Z0 ⊆ carrier := by
    intro e he
    rw [mem_cmp116Eq223PhysicalInteriorBonds_iff] at he
    exact Finset.mem_product.mpr ⟨he.1.1, Finset.mem_univ _⟩
  calc
    (cmp116Eq223PhysicalInteriorBonds
      (d := d) (M := M) (N' := N') Z0).card ≤ carrier.card :=
        Finset.card_le_card hsubset
    _ = (cmp116RegionSites Z0).card * d := by
      rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    _ ≤ (Z0.card * M ^ d) * d := by
      exact Nat.mul_le_mul_right d (card_cmp116RegionSites_le Z0)

/-- Explicit geometric dimension bound for the localized outer Gaussian.
This closes the cardinality conversion used after equation (2.25): the
remaining factor is linear in `Z0.card`, with constant
`M^d * d * (Nc^2 - 1)`. -/
theorem card_cmp116Eq223PhysicalLocalizedCoordinates_le
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (Z0 : Finset (FinBox d N')) :
    (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0).card ≤
      ((Z0.card * M ^ d) * d) * (Nc ^ 2 - 1) := by
  rw [Dict.card_cmp116Eq223PhysicalLocalizedCoordinates Z0]
  exact Nat.mul_le_mul_right (Nc ^ 2 - 1)
    (card_cmp116Eq223PhysicalInteriorBonds_le Z0)

/-- The physical localization projector retains an interior coordinate. -/
theorem physicalLocalizationProjection_mulVec_apply_of_interior
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (Z0 : Finset (FinBox d N'))
    (x : CMP116CoordIndex d L lieDim → ℝ)
    (qa : CMP116CoordIndex d L lieDim)
    (hqa : cmp116BondInterior Z0 (Dict.coordEquiv qa).1) :
    (cmp116Eq223CoordinateProjection
        (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ x) qa = x qa := by
  classical
  rw [cmp116Eq223CoordinateProjection, mulVec_diagonal]
  simp [cmp116Eq223PhysicalLocalizedCoordinates, hqa]

/-- The physical localization projector annihilates a non-interior
coordinate. -/
theorem physicalLocalizationProjection_mulVec_apply_of_not_interior
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (Z0 : Finset (FinBox d N'))
    (x : CMP116CoordIndex d L lieDim → ℝ)
    (qa : CMP116CoordIndex d L lieDim)
    (hqa : ¬cmp116BondInterior Z0 (Dict.coordEquiv qa).1) :
    (cmp116Eq223CoordinateProjection
        (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ x) qa = 0 := by
  classical
  rw [cmp116Eq223CoordinateProjection, mulVec_diagonal]
  simp [cmp116Eq223PhysicalLocalizedCoordinates, hqa]

/-- Exact quadratic form of the physical `P_Z0`, written as a sum over the
flattened coordinates selected by the physical bond-interior predicate. -/
theorem dotProduct_physicalLocalizationProjection_mulVec
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (Z0 : Finset (FinBox d N'))
    (x : CMP116CoordIndex d L lieDim → ℝ) :
    x ⬝ᵥ (cmp116Eq223CoordinateProjection
        (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ x) =
      ∑ qa ∈ Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0, x qa ^ 2 := by
  classical
  exact dotProduct_projection_mulVec _ _

/-- Source-facing positivity theorem with the physical block region `Z0`
itself as input.  No arbitrary flattened coordinate carrier remains. -/
theorem posDef_physicalRootMatrix_of_alpha5_covariance_half_small_physicalZ0
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    {precision covariance root :
      PhysicalGaugeOneCochain d (M * N') Nc →L[ℝ]
        PhysicalGaugeOneCochain d (M * N') Nc}
    {covNormBound rootNormBound : ℝ}
    {covWeight rootWeight :
      PhysicalBond d (M * N') → PhysicalBond d (M * N') → ℝ}
    (hcert : PhysicalLocalizedCovarianceRootCertificate
      precision covariance root covNormBound rootNormBound covWeight rootWeight)
    (Z0 : Finset (FinBox d N'))
    (alpha5 : ℝ) (halpha5 : 0 ≤ alpha5)
    (hsmall : alpha5 * covNormBound < (1 : ℝ) / 2) :
    (1 - (Dict.physicalRootMatrix root)ᵀ *
      (alpha5 • cmp116Eq223CoordinateProjection
        (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0)) *
      Dict.physicalRootMatrix root).PosDef := by
  exact Dict.posDef_physicalRootMatrix_of_alpha5_covariance_half_small
    hcert (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0)
    alpha5 halpha5 hsmall

/-- Canonical-core specialization of the physical Gaussian positivity
theorem.  The projector is now determined entirely by the physical `(D,P)`
localization data. -/
theorem posDef_physicalRootMatrix_of_alpha5_covariance_half_small_localizationCore
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    {precision covariance root :
      PhysicalGaugeOneCochain d (M * N') Nc →L[ℝ]
        PhysicalGaugeOneCochain d (M * N') Nc}
    {covNormBound rootNormBound : ℝ}
    {covWeight rootWeight :
      PhysicalBond d (M * N') → PhysicalBond d (M * N') → ℝ}
    (hcert : PhysicalLocalizedCovarianceRootCertificate
      precision covariance root covNormBound rootNormBound covWeight rootWeight)
    (Dset : Finset (Finset (FinBox d N')))
    (P : Finset (PhysicalBond d (M * N')))
    (alpha5 : ℝ) (halpha5 : 0 ≤ alpha5)
    (hsmall : alpha5 * covNormBound < (1 : ℝ) / 2) :
    (1 - (Dict.physicalRootMatrix root)ᵀ *
      (alpha5 • cmp116Eq223CoordinateProjection
        (Dict.cmp116Eq223PhysicalLocalizedCoordinates
          (cmp116LocalizationCore Dset P))) *
      Dict.physicalRootMatrix root).PosDef := by
  exact Dict.posDef_physicalRootMatrix_of_alpha5_covariance_half_small_physicalZ0
    hcert (cmp116LocalizationCore Dset P) alpha5 halpha5 hsmall

/-- Every Lie coordinate of a large-field bond belongs to the physical
localization projector whenever `Z0` is admissible for `(D,P)`. -/
theorem coordEquiv_symm_mem_physicalLocalizedCoordinates_of_mem_P
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    {Dset : Finset (Finset (FinBox d N'))}
    {P : Finset (PhysicalBond d (M * N'))}
    {Z0 : Finset (FinBox d N')}
    (hZ0 : CMP116LocalizationAdmissible Dset P Z0)
    {e : PhysicalBond d (M * N')} (heP : e ∈ P)
    (a : Fin (Nc ^ 2 - 1)) :
    Dict.coordEquiv.symm (e, a) ∈
      Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0 := by
  rw [Dict.mem_cmp116Eq223PhysicalLocalizedCoordinates_iff]
  simpa using hZ0.2 e heP

/-- Canonical-core specialization: all coordinates of every selected
large-field bond are retained by the projector built from the least admissible
localization region. -/
theorem coordEquiv_symm_mem_physicalLocalizedCoordinates_localizationCore
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (Dset : Finset (Finset (FinBox d N')))
    {P : Finset (PhysicalBond d (M * N'))}
    {e : PhysicalBond d (M * N')} (heP : e ∈ P)
    (a : Fin (Nc ^ 2 - 1)) :
    Dict.coordEquiv.symm (e, a) ∈
      Dict.cmp116Eq223PhysicalLocalizedCoordinates
        (cmp116LocalizationCore Dset P) := by
  exact Dict.coordEquiv_symm_mem_physicalLocalizedCoordinates_of_mem_P
    (cmp116LocalizationCore_admissible Dset P) heP a

end PhysicalGaugeCMP116Dictionary
end YangMills.RG
