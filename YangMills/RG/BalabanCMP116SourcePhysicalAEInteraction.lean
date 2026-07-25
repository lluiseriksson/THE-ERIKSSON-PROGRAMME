/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePhysicalBondField
import YangMills.RG.BalabanCMP116Eq221AEInteractionAbsorption

/-!
# Source-specific almost-everywhere interaction bound

This module joins the literal physical potential, the literal bond field,
the bilateral complex `R2` estimate, and a certified conditioned Gaussian
root.  The result is exactly the almost-everywhere interaction hypothesis
consumed by the equation-(2.23) inner integration.
-/

namespace YangMills.RG

open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.Operator

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

namespace CMP116Eq214PhysicalContourDensity

/-- Equations (2.20)--(2.22) on the actual conditioned Gaussian: the
potential and large-field maps are literal, while the complex `R2` cost is
the volume-uniform bilateral Schur budget. -/
theorem ae_interactionExponent_le_sourcePhysicalAlpha5
    {nDelta nY d M N' Nc L lieDim : ℕ}
    {Site : Type*} {Psi Phi : Site → Type*}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero (Nc ^ 2 - 1)] [NeZero L] [NeZero lieDim]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d (M * N')) Site Psi Phi
        (SUNLieCoord Nc) (Nc ^ 2 - 1))
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (D : Finset (Fin nY))
    (quadratic :
      (Fin nDelta → ℂ) →
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      Fin nY → PhysicalGaugeOneCochain d (M * N') Nc →
        PhysicalEndomorphism d (M * N') Nc)
    (remainder :
      (Fin nDelta → ℂ) →
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      Fin nY → PhysicalGaugeOneCochain d (M * N') Nc → ℝ)
    (amplitude residualWeight : Fin nY → ℝ)
    {kappa rowSum threshold potentialRate r2Rate gamma alpha : ℝ}
    (Z0 : Finset (FinBox d N'))
    (P : Finset (PhysicalBond d (M * N')))
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (conditionedCovariance :
      Matrix (PhysicalGaugeCoordIndex d (M * N') Nc)
        (PhysicalGaugeCoordIndex d (M * N') Nc) ℝ)
    (hroot :
      MatrixConditionedGaussianRootCertificate
        conditionedCovariance C.referenceRoot
        (cmp116SourcePhysicalLocalizedCoordinates Dict Z0))
    (hrowSum : 0 ≤ rowSum)
    (hrow : ∀ target : PhysicalBond d (M * N'),
      ∑ source : PhysicalBond d (M * N'),
        Real.exp (-(kappa *
          (physicalBondDist target source : ℝ))) ≤ rowSum)
    (hquadratic : ∀ b y, y ∈ D →
      PhysicalCovarianceExponentialKernelBound
        (quadratic sigma psi phi y
          (physicalBondProjection
            (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
            (cmp116SourcePhysicalCoordinateCochain b)))
        physicalBondDist (amplitude y) kappa)
    (hremainder : ∀ b y, y ∈ D →
      ‖tau y‖ *
          |remainder sigma psi phi y
            (physicalBondProjection
              (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
              (cmp116SourcePhysicalCoordinateCochain b))| ≤
        residualWeight y)
    (hpotentialRate :
      potentialRate =
        ∑ y ∈ D, ‖tau y‖ * amplitude y * rowSum)
    (hR2 :
      (‖C.r2Matrix sigma tau psi phi‖ +
        ‖(C.r2Matrix sigma tau psi phi).transpose‖) / 2 ≤ r2Rate)
    (hgamma : 0 ≤ gamma)
    (hbudget : potentialRate + r2Rate + gamma ≤ alpha) :
    let Csource :=
      (C.withSourcePhysicalComplexTauPotential
        Dict D quadratic remainder Z0).withSourcePhysicalBondField threshold
    ∀ᵐ b ∂matrixGaussianPi Csource.referenceRoot,
      (Csource.toLocalFiniteGaussianData.interactionExponent
          sigma tau psi phi b).re +
        gamma / 2 *
          (∑ bond ∈ P,
            ‖Csource.bondField b bond‖ ^ 2) ≤
        alpha / 2 *
          (∑ ba ∈ cmp116SourcePhysicalLocalizedCoordinates Dict Z0,
            b ba ^ 2) +
          ∑ y ∈ D, residualWeight y := by
  dsimp only
  let Cpotential :=
    C.withSourcePhysicalComplexTauPotential
      Dict D quadratic remainder Z0
  let Csource := Cpotential.withSourcePhysicalBondField threshold
  let S := cmp116SourcePhysicalLocalizedCoordinates Dict Z0
  let potentialRate' :=
    ∑ y ∈ D, ‖tau y‖ * amplitude y * rowSum
  have hpotential :
      ∀ᵐ b ∂matrixGaussianPi Csource.referenceRoot,
        (Csource.potential sigma tau psi phi b).re ≤
          potentialRate / 2 * (∑ ba ∈ S, b ba ^ 2) +
            ∑ y ∈ D, residualWeight y := by
    filter_upwards [] with b
    have hp :=
      C.re_withSourcePhysicalComplexTauPotential_potential_le_localized
        Dict D quadratic remainder amplitude residualWeight
        hrowSum hrow Z0 sigma tau psi phi b
        (hquadratic b) (hremainder b)
    simpa [Csource, Cpotential, S, potentialRate', hpotentialRate] using hp
  have hcutoff :
      ∀ᵐ b ∂matrixGaussianPi Csource.referenceRoot,
        (∑ bond ∈ P, ‖Csource.bondField b bond‖ ^ 2) ≤
          ∑ ba ∈ S, b ba ^ 2 := by
    filter_upwards [hroot.ae_supported] with b hb
    calc
      (∑ bond ∈ P, ‖Csource.bondField b bond‖ ^ 2) =
          ∑ bond ∈ P,
            ‖cmp116SourcePhysicalCoordinateCochain b bond‖ ^ 2 := by
              rfl
      _ ≤ ∑ ba, b ba ^ 2 :=
        sum_norm_sq_cmp116SourcePhysicalCoordinateCochain_le P b
      _ = ∑ ba ∈ S, b ba ^ 2 := hb.sum_sq_eq_sum_mem
  have hR2source :
      (‖Csource.r2Matrix sigma tau psi phi‖ +
        ‖(Csource.r2Matrix sigma tau psi phi).transpose‖) / 2 ≤ r2Rate := by
    simpa [Csource, Cpotential] using hR2
  have hresult :=
    cmp116Eq220_eq221_eq222_complexInteraction_le_localized_ae
      hroot (Csource.r2Matrix sigma tau psi phi)
      (fun b => Csource.potential sigma tau psi phi b)
      (fun b => ∑ bond ∈ P, ‖Csource.bondField b bond‖ ^ 2)
      potentialRate r2Rate gamma alpha
      (∑ y ∈ D, residualWeight y)
      hpotential hR2source hcutoff hgamma hbudget
  simpa [Csource, Cpotential, S] using hresult

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
