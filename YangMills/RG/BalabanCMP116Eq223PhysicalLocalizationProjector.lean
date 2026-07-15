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
