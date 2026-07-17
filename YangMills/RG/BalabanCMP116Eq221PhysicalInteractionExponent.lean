/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq221PhysicalCoordinateBridge

/-!
# Literal real CMP116 interaction exponent

This module replaces the free scalar called `interactionExponent` in the
real equation-(2.21) bridge by the literal potential and signed
`R₁/R₂/R₃` correction forms.  The orientations are those fixed by the
physical correction dictionary: `R₂ = K₀ - K₁` enters with positive one
half, while `R₃ = Γ₁ - Γ₀` enters with a minus sign.

Honest scope: this is the fixed-real-field exponent bounded before the
Cauchy continuation.  It is not the complex-valued
`CMP116Eq214AnalyticData.interactionExponent` field: that field has no outer
Gaussian coordinate, so the `X`-quadratic and `B`--`X` terms must later be
distributed between the outer weight and the Gaussian source.  No
complex-contour identification is claimed here.
-/

namespace YangMills.RG

open Matrix
open scoped BigOperators RealInnerProductSpace

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

namespace PhysicalGaugeCMP116Dictionary

/-- The literal real CMP116 interaction exponent at fixed Gaussian fields.
The stabilizing main Gaussian quadratic is deliberately absent: it belongs
to the covariance measure, not to the interaction potential. -/
noncomputable def cmp116Eq221PhysicalRealInteractionExponent
    {d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (Z0 : Finset (FinBox d N'))
    (R₁ R₂ R₃ : PhysicalEndomorphism d (M * N') Nc)
    (potential : PhysicalGaugeOneCochain d (M * N') Nc → ℝ)
    (x b : EuclideanSpace ℝ (CMP116CoordIndex d L lieDim)) : ℝ :=
  let S : Finset (PhysicalBond d (M * N')) :=
    cmp116Eq223PhysicalInteriorBonds Z0
  let X := physicalBondProjection S
    (Dict.flatPhysicalLinearIsometryEquiv x)
  let B := physicalBondProjection S
    (Dict.flatPhysicalLinearIsometryEquiv b)
  potential B +
    ((1 / 2 : ℝ) * inner ℝ X (R₁ X) +
      (1 / 2 : ℝ) * inner ℝ B (R₂ B) -
      inner ℝ B (R₃ X))

end PhysicalGaugeCMP116Dictionary

/-- The literal real exponent is absorbed into the canonical `alpha5`
budget with no `hshape` or `henergy` premise.  The only remaining functional
estimate here is equation (2.20) for the actual potential evaluated on the
localized physical fluctuation field. -/
theorem CMP116Eq216PhysicalKernelCertificate.physicalRealInteractionExponent_le_coordinateAlpha5_physicalCutoff_geometric
    {d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (Dset : Finset (Finset (FinBox d N')))
    (P : Finset (PhysicalBond d (M * N')))
    (Z0 : Finset (FinBox d N'))
    (hZ0 : CMP116LocalizationAdmissible Dset P Z0)
    {R₁ R₂ R₃ : PhysicalEndomorphism d (M * N') Nc}
    (cert : CMP116Eq216PhysicalKernelCertificate
      R₁ R₂ R₃ physicalBondDist)
    (hgeom :
      ((2 ^ d : ℕ) : ℝ) * Real.exp (-cert.rate) < 1)
    (x b : EuclideanSpace ℝ (CMP116CoordIndex d L lieDim))
    (potential : PhysicalGaugeOneCochain d (M * N') Nc → ℝ)
    {potentialRate cutoff alpha5 residual20 : ℝ}
    (hpotential :
      potential
          (physicalBondProjection
            (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
            (Dict.flatPhysicalLinearIsometryEquiv b)) ≤
        potentialRate / 2 *
          (b ⬝ᵥ
            (cmp116Eq223CoordinateProjection
              (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ b)) +
          residual20)
    (hpotentialRate : 0 ≤ potentialRate)
    (hcutoff : 0 ≤ cutoff)
    (hbudget :
      potentialRate +
          2 * (cert.amplitude *
            cmp116Eq221PhysicalRowSum d cert.rate) +
          cutoff ≤ alpha5) :
    Dict.cmp116Eq221PhysicalRealInteractionExponent
          Z0 R₁ R₂ R₃ potential x b +
        cutoff / 2 *
          (∑ qa ∈ Dict.cmp116Eq222SelectedCoordinates P, b qa ^ 2) ≤
      alpha5 / 2 *
          (x ⬝ᵥ
              (cmp116Eq223CoordinateProjection
                (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ x) +
            b ⬝ᵥ
              (cmp116Eq223CoordinateProjection
                (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ b)) +
        residual20 := by
  apply cert.interactionExponent_le_coordinateAlpha5_physicalCutoff_geometric
    Dict Dset P Z0 hZ0 hgeom x b
    (interactionExponent :=
      Dict.cmp116Eq221PhysicalRealInteractionExponent
        Z0 R₁ R₂ R₃ potential x b)
    (potentialTerm :=
      potential
        (physicalBondProjection
          (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
          (Dict.flatPhysicalLinearIsometryEquiv b)))
  · dsimp [PhysicalGaugeCMP116Dictionary.cmp116Eq221PhysicalRealInteractionExponent]
    have hR₁ := le_abs_self
      (inner ℝ
        (physicalBondProjection
          (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
          (Dict.flatPhysicalLinearIsometryEquiv x))
        (R₁ (physicalBondProjection
          (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
          (Dict.flatPhysicalLinearIsometryEquiv x))))
    have hR₂ := le_abs_self
      (inner ℝ
        (physicalBondProjection
          (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
          (Dict.flatPhysicalLinearIsometryEquiv b))
        (R₂ (physicalBondProjection
          (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
          (Dict.flatPhysicalLinearIsometryEquiv b))))
    have hR₃ := neg_le_abs
      (inner ℝ
        (physicalBondProjection
          (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
          (Dict.flatPhysicalLinearIsometryEquiv b))
        (R₃ (physicalBondProjection
          (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
          (Dict.flatPhysicalLinearIsometryEquiv x))))
    linarith
  · exact hpotential
  · exact hpotentialRate
  · exact hcutoff
  · exact hbudget

end

end YangMills.RG
