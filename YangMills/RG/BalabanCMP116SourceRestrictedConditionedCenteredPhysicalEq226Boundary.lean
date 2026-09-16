/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourceRestrictedConditionedPhysicalEq226Boundary
import YangMills.RG.BalabanCMP116SourceRestrictedConditionedCenteredPhysicalInteractionProducer

/-!
# Source-faithful centered physical equation-(2.26) boundary

This endpoint connects the literal radial estimates `(1.43)` and `(1.36)` to
the conditioned physical term weight.  The source contour remains centered
through Cauchy extraction, and the complete center-plus-displacement residual
is absorbed by its rooted local-volume ledger.
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

set_option maxHeartbeats 30000000 in
/-- Literal centered source estimates, the physical conditioned contour, and
the rooted full-residual ledger produce the equation-(2.26) term weight. -/
theorem
    norm_term_le_eq226SourceTermWeight_of_sourcePi4ConditionedCenteredPhysicalPotentialLedger
    {nDelta nY M Q Nc R Delta L lieDim q : ℕ}
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
    (total residual :
      (Fin nDelta → ℂ) →
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      Fin nY → PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc → ℝ)
    (hsmooth : ∀ sigma psi phi y,
      ContDiff ℝ 2
        (cmp116Eq142PhysicalQuadraticCore
          (total sigma psi phi) (residual sigma psi phi) y))
    (kernelSupport :
      Fin nY → PhysicalBond 4 (M * (2 * Q)) →
        PhysicalBond 4 (M * (2 * Q)) → Prop)
    (domainMetric : Fin nY → ℕ) (domainCard : Fin nY → ℕ)
    (domainSupport : Fin nY → Finset (FinBox 4 (2 * Q)))
    (Y0 P : Finset (PhysicalBond 4 (M * (2 * Q))))
    (psi : ∀ s, Psi s) (phi : ∀ s, Phi s)
    (E0 epsilon1 C1 alpha4 C3 C2 kappa1 delta kappa gk rowSum
      threshold alpha gamma : ℝ)
    (gapL gapCard : ℕ)
    {qBound : ℝ} (hq0 : 0 ≤ qBound) (hq1 : qBound < 1)
    (rootBound Calpha : ℝ)
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
    (hE0 : 0 < E0) (hepsilon1 : 0 < epsilon1)
    (hC1 : 0 < C1) (halpha4 : 0 < alpha4)
    (hC3 : 0 ≤ C3) (hC3upper : C3 ≤ E0 * C1)
    (hM : 1 ≤ M) (hq : 8 ≤ q) (hkappa1 : 1 < kappa1)
    (hkappa :
      (1 - 3 * delta) * kappa ≤ (1 / 8 : ℝ) * (kappa1 - 1))
    (hdomainDist : ∀ y : Fin nY, 0 ≤ (domainMetric y : ℝ))
    (hrow : ∀ target : PhysicalBond 4 (M * (2 * Q)),
      ∑ source : PhysicalBond 4 (M * (2 * Q)),
        Real.exp (-(cmp116Eq219InternalRate M kappa1 *
          (physicalBondDist target source : ℝ))) ≤ rowSum)
    (hgeometry : ∀ y source target,
      kernelSupport y source target →
        cmp116Eq219InternalRate M kappa1 *
            (physicalBondDist target source : ℝ) ≤
          (1 / 4 : ℝ) * (kappa1 - 1) * domainCard y)
    (hzeroB : ∀ sigma,
      CMP116Eq214ShiftedPolydisc nDelta C.deltaRadius sigma →
      ∀ b y source target,
      ¬ kernelSupport y source target →
        ∀ (v w : SUNLieCoord Nc), ∀ t ∈ Set.Icc (0 : ℝ) 1,
          cmp116FDerivHessian
            (cmp116Eq142PhysicalQuadraticCore
              (total sigma
                (restrictGlobal C.spectatorSupport psi)
                (restrictGlobal C.fluctuationSupport phi))
              (residual sigma
                (restrictGlobal C.spectatorSupport psi)
                (restrictGlobal C.fluctuationSupport phi)) y)
            (t • physicalBondProjection
              (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds
                Z0)
              (cmp116SourcePhysicalCoordinateCochain b))
            (singlePhysicalBondCochain
              (d := 4) (N := M * (2 * Q)) (Nc := Nc) source v)
            (singlePhysicalBondCochain
              (d := 4) (N := M * (2 * Q)) (Nc := Nc) target w) = 0)
    (h143 : ∀ sigma,
      CMP116Eq214ShiftedPolydisc nDelta C.deltaRadius sigma →
      ∀ b y source target (v w : SUNLieCoord Nc),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |cmp116FDerivHessian
          (cmp116Eq142PhysicalQuadraticCore
            (total sigma
              (restrictGlobal C.spectatorSupport psi)
              (restrictGlobal C.fluctuationSupport phi))
            (residual sigma
              (restrictGlobal C.spectatorSupport psi)
              (restrictGlobal C.fluctuationSupport phi)) y)
          (t • physicalBondProjection
            (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
            (cmp116SourcePhysicalCoordinateCochain b))
          (singlePhysicalBondCochain
            (d := 4) (N := M * (2 * Q)) (Nc := Nc) source v)
          (singlePhysicalBondCochain
            (d := 4) (N := M * (2 * Q)) (Nc := Nc) target w)| ≤
          cmp116Eq143QMajorant C3 epsilon1 M C2 kappa1
            (domainMetric y : ℝ) (domainCard y) * ‖v‖ * ‖w‖)
    (h136 : ∀ sigma,
      CMP116Eq214ShiftedPolydisc nDelta C.deltaRadius sigma →
      ∀ b y,
      (-1 : ℂ) ^ P.card *
          cmp116SmallFieldCutoff Y0 threshold
            (cmp116SourcePhysicalCoordinateCochain b) *
          cmp116LargeFieldCutoff P threshold
            (cmp116SourcePhysicalCoordinateCochain b) ≠ 0 →
      |residual sigma
        (restrictGlobal C.spectatorSupport psi)
        (restrictGlobal C.fluctuationSupport phi) y
        (physicalBondProjection
          (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
          (cmp116SourcePhysicalCoordinateCochain b))| ≤
        cmp116Eq136ResidualMajorant E0 epsilon1 C1 M q
          C2 kappa1 delta kappa (domainMetric y : ℝ))
    (hinteractionBudget :
      cmp116Eq220CenteredSourcePotentialRate Finset.univ
          (fun y => (domainMetric y : ℝ)) domainCard
          C3 epsilon1 M C2 kappa1 alpha4 rowSum +
        cmp116SourcePi4PhysicalComplexR2BilateralBound
          K Delta Ahead rho rate radius (1 + radius) +
        gamma ≤ alpha)
    (hDeltaRadius :
      let quadratic := fun sigma psi phi =>
        cmp116Eq142PhysicalSourceQuadratic
          (total sigma psi phi) (residual sigma psi phi)
          (hsmooth sigma psi phi)
      let Cphysical :=
        (C.withSourcePhysicalComplexTauPotential
          Dict Finset.univ quadratic residual Z0).withSourcePhysicalBondField
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
      let quadratic := fun sigma psi phi =>
        cmp116Eq142PhysicalSourceQuadratic
          (total sigma psi phi) (residual sigma psi phi)
          (hsmooth sigma psi phi)
      let Cphysical :=
        (C.withSourcePhysicalComplexTauPotential
          Dict Finset.univ quadratic residual Z0).withSourcePhysicalBondField
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
    (hgk : gk ≠ 0)
    (hthresholdEq :
      let quadratic := fun sigma psi phi =>
        cmp116Eq142PhysicalSourceQuadratic
          (total sigma psi phi) (residual sigma psi phi)
          (hsmooth sigma psi phi)
      let Cphysical :=
        (C.withSourcePhysicalComplexTauPotential
          Dict Finset.univ quadratic residual Z0).withSourcePhysicalBondField
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
        cmp116Eq220CenteredSourceResidualWeight
          (fun y => (domainMetric y : ℝ))
          E0 epsilon1 C1 M q C2 kappa1 delta kappa alpha4 Y ≤ rootBound)
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
    let quadratic := fun sigma psi phi =>
      cmp116Eq142PhysicalSourceQuadratic
        (total sigma psi phi) (residual sigma psi phi)
        (hsmooth sigma psi phi)
    let Cphysical :=
      (C.withSourcePhysicalComplexTauPotential
        Dict Finset.univ quadratic residual Z0).withSourcePhysicalBondField
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
  let quadratic := fun sigma psi phi =>
    cmp116Eq142PhysicalSourceQuadratic
      (total sigma psi phi) (residual sigma psi phi)
      (hsmooth sigma psi phi)
  let Cphysical :=
    (C.withSourcePhysicalComplexTauPotential
      Dict Finset.univ quadratic residual Z0).withSourcePhysicalBondField
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
      (by simpa [Cphysical, quadratic] using hconditionedRoot)
      hconditionedNondegenerate alpha gamma hq0 hq1
      domainMetric domainSupport
      (cmp116Eq220CenteredSourceResidualWeight
        (fun y => (domainMetric y : ℝ))
        E0 epsilon1 C1 M q C2 kappa1 delta kappa alpha4)
      gapL gapCard rootBound Calpha
      (by simpa [Cphysical, quadratic] using hDeltaRadius)
      hnormalizedGap
      (by simpa [Cphysical, quadratic] using hYRadius)
      hE0 hepsilon1 hC1 halpha4 hM hgk
      (by simpa [Cphysical, quadratic] using hthresholdEq)
      halpha hrootSmall hgamma
      (by simpa [Cphysical] using hthresholdNonneg)
      hOuterSmall
      (by
        simpa [Cphysical, quadratic] using
          C.ae_interactionBoundary_of_sourcePi4ConditionedCenteredPhysicalPotential
            Dict anchor contourCarrier Z0 Z hcarrier e K root
            hsourceRange hfiniteRange hc hmass hK hD
            hAhead hrho hrate hgeom Cert htri hDelta hDelta1
            hradius hradiusCap hseries hneumann hneumannTranspose
            total residual hsmooth kernelSupport domainMetric domainCard
            E0 epsilon1 C1 alpha4 C3 C2 kappa1 delta kappa rowSum threshold
            Y0 P psi phi conditionedCovariance hconditionedRoot
            hconditionedNondegenerate
            hE0 hepsilon1 hC1 halpha4 hC3 hC3upper hM hq hkappa1 hkappa
            hdomainDist
            (by
              simpa [Cphysical, quadratic] using hYRadius)
            hrow hgeometry hzeroB h143 h136 hgamma hinteractionBudget)
      (fun Y =>
        cmp116Eq220CenteredSourceResidualWeight_nonneg
          (fun y => (domainMetric y : ℝ))
          hE0.le hepsilon1.le hC1.le halpha4.le Y)
      hne hsub hrootNonneg hroot hvolumeBudget

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
