/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePhysicalAEInteraction
import YangMills.RG.BalabanCMP116SourcePi4FullComplexR2BilateralPhysicalBound
import YangMills.RG.BalabanCMP116SourceRestrictedConditionedPhysicalR3SourceRateProducer

/-!
# Physical AE interaction on the restricted source contour

This module constructs the equation-(2.20)--(2.22) almost-everywhere
interaction estimate on the literal restricted source contour.  The complex
`R2` budget is generated from the physical row and transpose Neumann bounds;
it is not supplied as a matrix estimate.
-/

namespace YangMills.RG

open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.Operator

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

namespace CMP116Eq214PhysicalContourDensity

set_option maxHeartbeats 2000000 in
/-- The literal source potential and bond field, the physical bilateral `R2`
bound, and the certified conditioned covariance root produce the AE
interaction bound on the inner carrier `Z0`, after restricting the outer
Gaussian to `Z`. -/
theorem
    ae_interactionExponent_le_sourcePi4RestrictedPhysicalAlpha5
    {nDelta nY M Q Nc R Delta L lieDim : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero L] [NeZero lieDim]
    {Site : Type*} {Psi Phi : Site → Type*}
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond 4 (M * (2 * Q))) Site Psi Phi
        (SUNLieCoord Nc) (Nc ^ 2 - 1))
    (Dict : PhysicalGaugeCMP116Dictionary
      4 (M * (2 * Q)) Nc 4 L lieDim)
    (anchor : FinBox 4 Q)
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (hcarrier : contourCarrier ⊆ cmp116SourceSigmaZero anchor)
    (e : Fin nDelta ≃ ↥contourCarrier)
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (K root : PhysicalEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hfiniteRange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          hc hmass hK‖ < 1)
    {Ahead rho rate radius : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hDelta : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Delta)
    (hDelta1 : 1 ≤ Delta)
    (hradius : 0 ≤ radius)
    (hradiusCap : ∀ i, 1 + C.deltaRadius i ≤ radius)
    (hseries :
      ‖cmp116SourcePi4ComplexContourRatio
        Delta rho (1 + radius)‖ < 1)
    (hneumann :
      ‖cmp116PhysicalEndomorphismComplexMatrix K‖ *
        cmp116SourcePi4PhysicalComplexContourDefectBound
          Nc Delta Ahead rho rate radius (1 + radius) < 1)
    (hneumannTranspose :
      cmp116SourcePi4PhysicalComplexTransposeRelativeDefectBound
        K Delta Ahead rho rate radius (1 + radius) < 1)
    (D : Finset (Fin nY))
    (quadratic :
      (Fin nDelta → ℂ) →
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      Fin nY → PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →
        PhysicalEndomorphism M Q Nc)
    (remainder :
      (Fin nDelta → ℂ) →
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      Fin nY → PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc → ℝ)
    (amplitude residualWeight : Fin nY → ℝ)
    {kappa rowSum threshold potentialRate gamma alpha : ℝ}
    (P : Finset (PhysicalBond 4 (M * (2 * Q))))
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : ∀ s, Psi s) (phi : ∀ s, Phi s)
    (hsigma : CMP116Eq214ShiftedPolydisc nDelta C.deltaRadius sigma)
    (conditionedCovariance :
      Matrix
        (PhysicalGaugeCoordIndex 4 (M * (2 * Q)) Nc)
        (PhysicalGaugeCoordIndex 4 (M * (2 * Q)) Nc) ℝ)
    (hroot :
      MatrixConditionedGaussianRootCertificate
        conditionedCovariance
        (cmp116PhysicalEndomorphismRealMatrix root)
        (cmp116SourcePhysicalLocalizedCoordinates Dict Z0))
    (hrowSum : 0 ≤ rowSum)
    (hrow : ∀ target : PhysicalBond 4 (M * (2 * Q)),
      ∑ source : PhysicalBond 4 (M * (2 * Q)),
        Real.exp (-(kappa *
          (physicalBondDist target source : ℝ))) ≤ rowSum)
    (hquadratic : ∀ b y, y ∈ D →
      PhysicalCovarianceExponentialKernelBound
        (quadratic sigma
          (restrictGlobal C.spectatorSupport psi)
          (restrictGlobal C.fluctuationSupport phi) y
          (physicalBondProjection
            (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
            (cmp116SourcePhysicalCoordinateCochain b)))
        physicalBondDist (amplitude y) kappa)
    (hremainder : ∀ b y, y ∈ D →
      ‖tau y‖ *
          |remainder sigma
            (restrictGlobal C.spectatorSupport psi)
            (restrictGlobal C.fluctuationSupport phi) y
            (physicalBondProjection
              (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
              (cmp116SourcePhysicalCoordinateCochain b))| ≤
        residualWeight y)
    (hpotentialRate :
      (∑ y ∈ D, ‖tau y‖ * amplitude y * rowSum) ≤ potentialRate)
    (hgamma : 0 ≤ gamma)
    (hbudget :
      potentialRate +
          cmp116SourcePi4PhysicalComplexR2BilateralBound
            K Delta Ahead rho rate radius (1 + radius) +
          gamma ≤ alpha) :
    let Craw :=
      C.withSourcePi4RestrictedComplexGaussianOfPhysicalContour
        anchor contourCarrier hcarrier e Z0 K root
        hsourceRange hfiniteRange hc hmass hK hD
        hAhead hrho hrate hgeom Cert htri hDelta hDelta1
        hradius hradiusCap hseries hneumann
    let Cphysical :=
      (Craw.withSourcePhysicalComplexTauPotential
        Dict D quadratic remainder Z0).withSourcePhysicalBondField threshold
    ∀ᵐ b ∂matrixGaussianPi Cphysical.referenceRoot,
      (Cphysical.toLocalFiniteGaussianData.interactionExponent
          sigma tau
            (restrictGlobal Cphysical.spectatorSupport psi)
            (restrictGlobal Cphysical.fluctuationSupport phi)
            b).re +
        gamma / 2 *
          (∑ bond ∈ P, ‖Cphysical.bondField b bond‖ ^ 2) ≤
        alpha / 2 *
          (∑ ba ∈ cmp116SourcePhysicalLocalizedCoordinates Dict Z0,
            b ba ^ 2) +
          ∑ y ∈ D, residualWeight y := by
  dsimp only
  let Craw :=
    C.withSourcePi4RestrictedComplexGaussianOfPhysicalContour
      anchor contourCarrier hcarrier e Z0 K root
      hsourceRange hfiniteRange hc hmass hK hD
      hAhead hrho hrate hgeom Cert htri hDelta hDelta1
      hradius hradiusCap hseries hneumann
  let Cphysical :=
    (Craw.withSourcePhysicalComplexTauPotential
      Dict D quadratic remainder Z0).withSourcePhysicalBondField threshold
  let SInner := cmp116SourcePhysicalLocalizedCoordinates Dict Z0
  have hdiff : ∀ d,
      ‖cmp116SourceRestrictedShiftedCoupling
        contourCarrier e sigma d - 1‖ ≤ radius :=
    norm_cmp116SourceRestrictedShiftedCoupling_sub_one_le_radius
      contourCarrier e C.deltaRadius radius hradius hradiusCap sigma hsigma
  have hcap : ∀ d,
      ‖cmp116SourceRestrictedShiftedCoupling contourCarrier e sigma d‖ ≤
        1 + radius :=
    norm_cmp116SourceRestrictedShiftedCoupling_le_one_add_radius
      contourCarrier e C.deltaRadius radius hradius hradiusCap sigma hsigma
  have hR2raw :=
    bilateral_cmp116SourcePi4FullComplexR2Matrix_le_physical
      anchor K hsourceRange hfiniteRange hc hmass hK hD
      hAhead hrho hrate hgeom Cert htri hDelta hDelta1
      (cmp116SourceRestrictedShiftedCoupling contourCarrier e sigma)
      hradius (by linarith) hdiff hcap hseries hneumann hneumannTranspose
  have hR2 :
      (‖Craw.r2Matrix sigma tau
          (restrictGlobal Craw.spectatorSupport psi)
          (restrictGlobal Craw.fluctuationSupport phi)‖ +
        ‖(Craw.r2Matrix sigma tau
          (restrictGlobal Craw.spectatorSupport psi)
          (restrictGlobal Craw.fluctuationSupport phi)).transpose‖) / 2 ≤
          cmp116SourcePi4PhysicalComplexR2BilateralBound
            K Delta Ahead rho rate radius (1 + radius) := by
    simpa [Craw] using hR2raw
  have hinner :=
    Craw.ae_interactionExponent_le_sourcePhysicalAlpha5
      (kappa := kappa) (rowSum := rowSum) (threshold := threshold)
      (potentialRate := potentialRate)
      (r2Rate :=
        cmp116SourcePi4PhysicalComplexR2BilateralBound
          K Delta Ahead rho rate radius (1 + radius))
      (gamma := gamma) (alpha := alpha)
      Dict D quadratic remainder amplitude residualWeight
      Z0 P sigma tau
      (restrictGlobal Craw.spectatorSupport psi)
      (restrictGlobal Craw.fluctuationSupport phi)
      conditionedCovariance
      (by simpa [Craw] using hroot)
      hrowSum hrow hquadratic hremainder hpotentialRate hR2
      hgamma hbudget
  simpa [Cphysical, Craw, SInner] using hinner

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
