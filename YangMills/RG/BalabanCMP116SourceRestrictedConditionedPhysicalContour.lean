/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourceRestrictedPhysicalContourDensity
import YangMills.RG.BalabanCMP116SourcePhysicalCoordinateDictionary
import YangMills.RG.BalabanCMP116Eq214ConditionedOuterCarrier

/-!
# The source-specific conditioned outer contour

The localized term in CMP116 equation (2.23) integrates the outer product
Gaussian as `dmu0(X)|_Z`.  The source operator itself remains

`Gamma = C_elim^T K (C_elim P_(Z0^c)) root`.

This module combines those two distinct facts.  It installs the literal
source-specific contour first and then precomposes only its outer variable by
the physical scalar carrier associated with `Z`.  In particular, `Z0`
continues to control the inner-field and complement factors, while `Z`
controls the outer Gaussian field.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

namespace CMP116Eq214PhysicalContourDensity

/-- Install the literal restricted complex contour and then restrict its
outer Gaussian variable to the physical carrier of `Z`. -/
def withSourcePi4RestrictedConditionedComplexGaussian
    {nDelta nY M Q Nc R L lieDim : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero L] [NeZero lieDim]
    {Site E : Type*} {Psi Phi : Site → Type*} [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond 4 (M * (2 * Q))) Site Psi Phi E (Nc ^ 2 - 1))
    (Dict : PhysicalGaugeCMP116Dictionary
      4 (M * (2 * Q)) Nc 4 L lieDim)
    (anchor : FinBox 4 Q)
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (hcarrier : contourCarrier ⊆ cmp116SourceSigmaZero anchor)
    (e : Fin nDelta ≃ ↥contourCarrier)
    (Z0 Z : Finset (FinBox 4 (2 * Q)))
    (K root : PhysicalEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          hc hmass hK‖ < 1)
    (hcontour : ∀ z,
      CMP116Eq214ShiftedPolydisc nDelta C.deltaRadius z →
      (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
          (R := R) anchor K hc hmass hK
          (cmp116SourceRestrictedShiftedCoupling
            contourCarrier e z)).det ≠ 0) :
    CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond 4 (M * (2 * Q))) Site Psi Phi E (Nc ^ 2 - 1) :=
  (C.withSourcePi4RestrictedComplexGaussian
      anchor contourCarrier hcarrier e Z0 K root
      hsourceRange hrange hc hmass hK hD hcontour).withConditionedOuterCarrier
    (cmp116SourcePhysicalLocalizedCoordinates Dict Z)

/-- The canonical `R3` source of the source-specific conditioned contour has
the exact `Z`-localized energy bound.  No support condition on the covariance
root is used. -/
theorem dotProduct_sourcePi4RestrictedConditioned_r3RealSource_self_le
    {nDelta nY M Q Nc R L lieDim : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero L] [NeZero lieDim]
    {Site E : Type*} {Psi Phi : Site → Type*} [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond 4 (M * (2 * Q))) Site Psi Phi E (Nc ^ 2 - 1))
    (Dict : PhysicalGaugeCMP116Dictionary
      4 (M * (2 * Q)) Nc 4 L lieDim)
    (anchor : FinBox 4 Q)
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (hcarrier : contourCarrier ⊆ cmp116SourceSigmaZero anchor)
    (e : Fin nDelta ≃ ↥contourCarrier)
    (Z0 Z : Finset (FinBox 4 (2 * Q)))
    (K root : PhysicalEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          hc hmass hK‖ < 1)
    (hcontour : ∀ z,
      CMP116Eq214ShiftedPolydisc nDelta C.deltaRadius z →
      (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
          (R := R) anchor K hc hmass hK
          (cmp116SourceRestrictedShiftedCoupling
            contourCarrier e z)).det ≠ 0)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (x : CMP116Eq214GaussianCoordinate
      (PhysicalBond 4 (M * (2 * Q))) (Nc ^ 2 - 1)) :
    let Craw :=
      C.withSourcePi4RestrictedComplexGaussian
        anchor contourCarrier hcarrier e Z0 K root
        hsourceRange hrange hc hmass hK hD hcontour
    let Csource :=
      C.withSourcePi4RestrictedConditionedComplexGaussian Dict
        anchor contourCarrier hcarrier e Z0 Z K root
        hsourceRange hrange hc hmass hK hD hcontour
    Csource.r3RealSource sigma tau psi phi x ⬝ᵥ
        Csource.r3RealSource sigma tau psi phi x ≤
      ‖cmp116Eq214RealPartMatrix
          (Craw.r3Matrix sigma tau psi phi)‖ ^ 2 *
        ∑ i ∈ cmp116SourcePhysicalLocalizedCoordinates Dict Z, x i ^ 2 := by
  dsimp only
  exact
    (C.withSourcePi4RestrictedComplexGaussian
      anchor contourCarrier hcarrier e Z0 K root
      hsourceRange hrange hc hmass hK hD hcontour
    ).dotProduct_conditionedOuterCarrier_r3RealSource_self_le
      (cmp116SourcePhysicalLocalizedCoordinates Dict Z) sigma tau psi phi x

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
