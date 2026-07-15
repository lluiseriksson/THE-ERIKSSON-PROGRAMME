/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq220PotentialQuadratic
import YangMills.RG.BalabanCMP116Eq222CutoffSuppression

/-!
# Physical equation-(2.20)/(2.22) absorption

This small joining module keeps the reusable Schur estimate independent of the
large physical equation-(2.14) data stack.  It specializes the scalar
coefficient ledger to the canonical CMP116 localization projector.
-/

namespace YangMills.RG

open Matrix
open scoped BigOperators

noncomputable section

/-- Physical-projector specialization of the absorption step.  Admissibility
supplies `energyP <= <x,P_Z0 x>` from the literal equation-(2.22) coordinate
carrier, so no independent projector-comparison hypothesis remains. -/
theorem PhysicalGaugeCMP116Dictionary.cmp116Eq220_eq222_absorb_into_physicalLocalization
    {d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    {Dset : Finset (Finset (FinBox d N'))}
    {P : Finset (PhysicalBond d (M * N'))}
    {Z0 : Finset (FinBox d N')}
    (hZ0 : CMP116LocalizationAdmissible Dset P Z0)
    (x : CMP116CoordIndex d L lieDim → ℝ)
    {interaction kernelRate gamma alpha5 residual : ℝ}
    (hinteraction :
      interaction ≤ kernelRate / 2 *
        (x ⬝ᵥ (cmp116Eq223CoordinateProjection
          (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ x)) + residual)
    (hgamma : 0 ≤ gamma)
    (hbudget : kernelRate + gamma ≤ alpha5) :
    interaction + gamma / 2 *
        (∑ qa ∈ Dict.cmp116Eq222SelectedCoordinates P, x qa ^ 2) ≤
      alpha5 / 2 *
        (x ⬝ᵥ (cmp116Eq223CoordinateProjection
          (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ x)) + residual := by
  apply cmp116Eq220_eq222_absorb_into_alpha5_localized
    hinteraction
    (Dict.sum_sq_selectedCoordinates_le_dotProduct_physicalLocalizationProjection
      hZ0 x)
    hgamma
  · rw [Dict.dotProduct_physicalLocalizationProjection_mulVec]
    positivity
  · exact hbudget

end

end YangMills.RG
