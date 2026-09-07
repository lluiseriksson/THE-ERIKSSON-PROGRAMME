/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourceRestrictedConditionedPhysicalEq226Boundary
import YangMills.RG.BalabanCMP116SourceRestrictedConditionedPhysicalInteractionProducer

/-!
# Equation (2.26) with the physical interaction generated internally

This is the strong source-facing equation-(2.26) boundary.  Unlike the
compositional theorem below it, this endpoint does not receive an
almost-everywhere interaction estimate.  It constructs that estimate from
the literal source potential, the physical bilateral `R2` estimate, the
literal bond field, and the conditioned covariance-root certificate.
-/

namespace YangMills.RG

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

namespace CMP116Eq214PhysicalContourDensity

set_option maxHeartbeats 20000000 in
/-- The physical source potential and conditioned covariance certificate,
together with the existing outer and rooted residual ledgers, produce the
literal equation-(2.26) term weight.  No `hinteraction` premise occurs. -/
theorem
    norm_term_le_eq226SourceTermWeight_of_sourcePi4ConditionedPhysicalPotentialLedger
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
    (contourCarrier Z0 Z : Finset (FinBox 4 (2 * Q)))
    (hcarrier : contourCarrier ⊆ cmp116SourceSigmaZero anchor)
    (hcarrierZ0 : contourCarrier ⊆ Z0)
    (hZ0Z : Z0 ⊆ Z)
    (e : Fin nDelta ≃ ↥contourCarrier)
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
      ‖cmp116SourcePi4ComplexContourRatio Delta rho (1 + radius)‖ < 1)
    (hneumann :
      ‖cmp116PhysicalEndomorphismComplexMatrix K‖ *
        cmp116SourcePi4PhysicalComplexContourDefectBound
          Nc Delta Ahead rho rate radius (1 + radius) < 1)
    (hneumannTranspose :
      cmp116SourcePi4PhysicalComplexTransposeRelativeDefectBound
        K Delta Ahead rho rate radius (1 + radius) < 1)
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
    (amplitude : Fin nY → ℝ)
    (Y0 P : Finset (PhysicalBond 4 (M * (2 * Q))))
    (psi : ∀ s, Psi s) (phi : ∀ s, Phi s)
    (alpha gamma : ℝ)
    {qBound : ℝ} (hq0 : 0 ≤ qBound) (hq1 : qBound < 1)
    {E0 epsilon1 C1 alpha4 : ℝ} {q : ℕ}
    {C2 kappa1 delta kappa gk : ℝ}
    (domainMetric : Fin nY → ℕ)
    (domainSupport : Fin nY → Finset (FinBox 4 (2 * Q)))
    (gapL gapCard : ℕ)
    (rootBound Calpha rowSum threshold potentialRate : ℝ)
    (conditionedCovariance :
      Matrix
        (PhysicalGaugeCoordIndex 4 (M * (2 * Q)) Nc)
        (PhysicalGaugeCoordIndex 4 (M * (2 * Q)) Nc) ℝ)
    (hconditionedRoot :
      MatrixConditionedGaussianRootCertificate
        conditionedCovariance
        (cmp116PhysicalEndomorphismRealMatrix root)
        (cmp116SourcePhysicalLocalizedCoordinates Dict Z0))
    (hconditionedNondegenerate :
      MatrixConditionedGaussianCovarianceLowerCertificate
        conditionedCovariance
        (cmp116SourcePhysicalLocalizedCoordinates Dict Z0))
    (hrowSum : 0 ≤ rowSum)
    (hrow : ∀ target : PhysicalBond 4 (M * (2 * Q)),
      ∑ source : PhysicalBond 4 (M * (2 * Q)),
        Real.exp (-(kappa *
          (physicalBondDist target source : ℝ))) ≤ rowSum)
    (hquadratic : ∀ sigma,
      CMP116Eq214ShiftedPolydisc nDelta C.deltaRadius sigma →
      ∀ b y,
        PhysicalCovarianceExponentialKernelBound
          (quadratic sigma
            (restrictGlobal C.spectatorSupport psi)
            (restrictGlobal C.fluctuationSupport phi) y
            (physicalBondProjection
              (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
              (cmp116SourcePhysicalCoordinateCochain b)))
          physicalBondDist (amplitude y) kappa)
    (hremainder : ∀ sigma tau,
      CMP116Eq214ShiftedPolydisc nDelta C.deltaRadius sigma →
      CMP116Eq214ShiftedPolydisc nY C.yRadius tau →
      ∀ b y,
        ‖tau y‖ *
            |remainder sigma
              (restrictGlobal C.spectatorSupport psi)
              (restrictGlobal C.fluctuationSupport phi) y
              (physicalBondProjection
                (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
                (cmp116SourcePhysicalCoordinateCochain b))| ≤
          cmp116Eq220ResidualDomainWeight alpha4 delta kappa
            (domainMetric y : ℝ))
    (hpotentialRate : ∀ tau,
      CMP116Eq214ShiftedPolydisc nY C.yRadius tau →
      (∑ y : Fin nY, ‖tau y‖ * amplitude y * rowSum) ≤ potentialRate)
    (hinteractionBudget :
      potentialRate +
          cmp116SourcePi4PhysicalComplexR2BilateralBound
            K Delta Ahead rho rate radius (1 + radius) +
          gamma ≤ alpha)
    (hDeltaRadius :
      let Cphysical :=
        (C.withSourcePhysicalComplexTauPotential
          Dict Finset.univ quadratic remainder Z0).withSourcePhysicalBondField
            threshold
      (Cphysical.withSourcePi4RestrictedComplexGaussianOfPhysicalContour
        anchor contourCarrier hcarrier e Z0 K root
        hsourceRange hfiniteRange hc hmass hK hD
        hAhead hrho hrate hgeom Cert htri hDelta hDelta1
        hradius (by simpa [Cphysical] using hradiusCap)
        hseries hneumann).deltaRadius =
          fun _ => cmp116Eq214SigmaCauchyRadius kappa1)
    (hnormalizedGap :
      ((((gapL * M : ℕ) : ℝ) ^ 4)⁻¹ * (gapCard : ℝ)) =
        (nDelta : ℝ))
    (hYRadius :
      let Cphysical :=
        (C.withSourcePhysicalComplexTauPotential
          Dict Finset.univ quadratic remainder Z0).withSourcePhysicalBondField
            threshold
      (Cphysical.withSourcePi4RestrictedComplexGaussianOfPhysicalContour
        anchor contourCarrier hcarrier e Z0 K root
        hsourceRange hfiniteRange hc hmass hK hD
        hAhead hrho hrate hgeom Cert htri hDelta hDelta1
        hradius (by simpa [Cphysical] using hradiusCap)
        hseries hneumann).yRadius =
          fun Y =>
            cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
              C2 kappa1 delta kappa (domainMetric Y : ℝ))
    (hE0 : 0 < E0) (hepsilon1 : 0 < epsilon1)
    (hC1 : 0 < C1) (halpha4 : 0 < alpha4) (hM : 1 ≤ M)
    (hgk : gk ≠ 0)
    (hthresholdEq :
      let Cphysical :=
        (C.withSourcePhysicalComplexTauPotential
          Dict Finset.univ quadratic remainder Z0).withSourcePhysicalBondField
            threshold
      (Cphysical.withSourcePi4RestrictedComplexGaussianOfPhysicalContour
        anchor contourCarrier hcarrier e Z0 K root
        hsourceRange hfiniteRange hc hmass hK hD
        hAhead hrho hrate hgeom Cert htri hDelta hDelta1
        hradius (by simpa [Cphysical] using hradiusCap)
        hseries hneumann).threshold = epsilon1 / gk)
    (halpha : 0 ≤ alpha)
    (hrootSmall :
      alpha *
        (@norm
          (Matrix
            (PhysicalBond 4 (M * (2 * Q)) × Fin (Nc ^ 2 - 1))
            (PhysicalBond 4 (M * (2 * Q)) × Fin (Nc ^ 2 - 1)) ℝ)
          Matrix.instL2OpNormedAddCommGroup.toNorm
          (cmp116PhysicalEndomorphismRealMatrix root)) ^ 2 < 1)
    (hgamma : 0 ≤ gamma)
    (hthresholdNonneg : 0 ≤ threshold)
    (hOuterSmall :
      2 *
        (cmp116SourcePi4PhysicalComplexR1DefectBilateralBudget
            K root hc hmass hK Z0 Delta Ahead rho rate radius (1 + radius) +
          |cmp116Eq225SourceCoefficient
              (cmp116PhysicalEndomorphismRealMatrix root) alpha *
            cmp116SourcePi4PhysicalComplexR3SourceRate
              K root Z0 Delta Ahead rho rate radius (1 + radius)|) ≤
        qBound)
    (hne : ∀ Y : Fin nY, (domainSupport Y).Nonempty)
    (hsub : ∀ Y : Fin nY, domainSupport Y ⊆ Z0)
    (hrootNonneg : 0 ≤ rootBound)
    (hroot : ∀ i ∈ Z0,
      ∑ Y ∈ (Finset.univ.filter fun Y : Fin nY =>
          i ∈ domainSupport Y),
        cmp116Eq220ResidualDomainWeight alpha4 delta kappa
          (domainMetric Y : ℝ) ≤ rootBound)
    (hvolumeBudget :
      rootBound +
          cmp116SourceRestrictedConditionedPhysicalOuterPerCarrierCost
            K root hc hmass hK Z0 Delta radius rate Ahead rho
              alpha
              (cmp116SourcePi4PhysicalComplexR3SourceRate
                K root Z0 Delta Ahead rho rate radius (1 + radius))
              qBound
              (cmp116SourceRestrictedUniformContourDeterminantCost
                M Nc Delta radius (1 + radius) rate Ahead rho
                  ‖cmp116PhysicalEndomorphismComplexMatrix K‖) ≤
        Calpha * alpha) :
    let Cphysical :=
      (C.withSourcePhysicalComplexTauPotential
        Dict Finset.univ quadratic remainder Z0).withSourcePhysicalBondField
          threshold
    let Craw :=
      Cphysical.withSourcePi4RestrictedComplexGaussianOfPhysicalContour
        anchor contourCarrier hcarrier e Z0 K root
        hsourceRange hfiniteRange hc hmass hK hD
        hAhead hrho hrate hgeom Cert htri hDelta hDelta1
        hradius (by simpa [Cphysical] using hradiusCap)
        hseries hneumann
    let SOuter := cmp116SourcePhysicalLocalizedCoordinates Dict Z
    let Csource := Craw.withConditionedOuterCarrier SOuter
    ‖Csource.toLocalFiniteGaussianData.toFiniteGaussianData.toAnalyticData.term
        Y0 P psi phi‖ ≤
      cmp116Eq226SourceTermWeight E0 epsilon1 C1 alpha4 M q
        C2 kappa1 delta kappa gamma gk gapL gapCard
        Calpha alpha Z.card domainMetric Finset.univ P := by
  dsimp only
  let Cphysical :=
    (C.withSourcePhysicalComplexTauPotential
      Dict Finset.univ quadratic remainder Z0).withSourcePhysicalBondField
        threshold
  have hradiusCapPhysical : ∀ i,
      1 + Cphysical.deltaRadius i ≤ radius := by
    simpa [Cphysical] using hradiusCap
  apply
    Cphysical.norm_term_le_eq226SourceTermWeight_of_sourcePi4ConditionedPhysicalOuterResidualLedger
      Dict anchor contourCarrier Z0 Z hcarrier hcarrierZ0 hZ0Z e K root
      hsourceRange hfiniteRange hc hmass hK hD
      hAhead hrho hrate hgeom Cert htri hDelta hDelta1
      hradius hradiusCapPhysical hseries hneumann hneumannTranspose
      Y0 P psi phi conditionedCovariance
      (by simpa [Cphysical] using hconditionedRoot)
      hconditionedNondegenerate alpha gamma hq0 hq1
      domainMetric domainSupport
      (fun Y =>
        cmp116Eq220ResidualDomainWeight alpha4 delta kappa
          (domainMetric Y : ℝ))
      gapL gapCard rootBound Calpha
      (by simpa [Cphysical] using hDeltaRadius)
      hnormalizedGap
      (by simpa [Cphysical] using hYRadius)
      hE0 hepsilon1 hC1 halpha4 hM hgk
      (by simpa [Cphysical] using hthresholdEq)
      halpha hrootSmall hgamma
      (by simpa [Cphysical] using hthresholdNonneg)
      hOuterSmall
      (by
        have hold :=
          C.ae_interactionBoundary_of_sourcePi4ConditionedPhysicalPotential
            (alpha4 := alpha4) (delta := delta) (kappa := kappa)
            (rowSum := rowSum) (threshold := threshold)
            (potentialRate := potentialRate) (gamma := gamma) (alpha := alpha)
            Dict anchor contourCarrier Z0 Z hcarrier e K root
            hsourceRange hfiniteRange hc hmass hK hD
            hAhead hrho hrate hgeom Cert htri hDelta hDelta1
            hradius hradiusCap hseries hneumann hneumannTranspose
            quadratic remainder amplitude domainMetric P psi phi
            conditionedCovariance hconditionedRoot hrowSum hrow
            hquadratic hremainder hpotentialRate hgamma hinteractionBudget
        dsimp only at hold ⊢
        intro sigma tau hsigma htau
        filter_upwards [hold sigma tau hsigma htau.toShifted] with b hb
        intro _
        exact hb)
      (fun Y =>
        mul_nonneg halpha4.le (Real.exp_nonneg _))
      hne hsub hrootNonneg hroot hvolumeBudget

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
