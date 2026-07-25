/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourceRestrictedConditionedPhysicalOuterBoundary
import YangMills.RG.BalabanCMP116Eq225ConditionedOuterTraceInteractionResidual

/-!
# Residual-preserving conditioned physical outer boundary

This theorem keeps the equation-(1.36)/(2.22) scalar outside both Gaussian
integrations while using `Z`, rather than `Z0`, as the outer carrier.
-/

namespace YangMills.RG

noncomputable section

open Matrix MeasureTheory
open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

namespace CMP116Eq214PhysicalContourDensity

set_option maxHeartbeats 18000000 in
theorem nestedCauchyBoundaryBound_of_sourcePi4ConditionedPhysicalOuterResidual
    {nDelta nY M Q Nc R Delta L lieDim : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero L] [NeZero lieDim]
    {Site E : Type*} {Psi Phi : Site → Type*} [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond 4 (M * (2 * Q))) Site Psi Phi E (Nc ^ 2 - 1))
    (Dict : PhysicalGaugeCMP116Dictionary
      4 (M * (2 * Q)) Nc 4 L lieDim)
    (anchor : FinBox 4 Q)
    (contourCarrier Z0 Z : Finset (FinBox 4 (2 * Q)))
    (hcarrier : contourCarrier ⊆ cmp116SourceSigmaZero anchor)
    (hcarrierZ0 : contourCarrier ⊆ Z0)
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
    (hDelta : ∀ y, (cmp116CoarseFaceAdj 4 Q).degree y ≤ Delta)
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
    (Y0 P : Finset (PhysicalBond 4 (M * (2 * Q))))
    (psi : ∀ s, Psi s) (phi : ∀ s, Phi s)
    (alpha gamma residual : ℝ)
    (halpha : 0 ≤ alpha)
    (hrootSmall :
      alpha *
        (@norm
          (Matrix
            (PhysicalBond 4 (M * (2 * Q)) × Fin (Nc ^ 2 - 1))
            (PhysicalBond 4 (M * (2 * Q)) × Fin (Nc ^ 2 - 1)) ℝ)
          Matrix.instL2OpNormedAddCommGroup.toNorm
          (cmp116PhysicalEndomorphismRealMatrix root)) ^ 2 < 1)
    (hgamma : 0 ≤ gamma) (hthreshold : 0 ≤ C.threshold)
    {qBound : ℝ} (hq0 : 0 ≤ qBound) (hq1 : qBound < 1)
    (hOuterSmall :
      2 *
        (cmp116SourcePi4PhysicalComplexR1DefectBilateralBudget
            K root hc hmass hK Z0 Delta Ahead rho rate radius (1 + radius) +
          |cmp116Eq225SourceCoefficient
              (cmp116PhysicalEndomorphismRealMatrix root) alpha *
            cmp116SourcePi4PhysicalComplexR3SourceRate
              K root Z0 Delta Ahead rho rate radius (1 + radius)|) ≤
        qBound) :
    let Craw :=
      C.withSourcePi4RestrictedComplexGaussianOfPhysicalContour
        anchor contourCarrier hcarrier e Z0 K root
        hsourceRange hfiniteRange hc hmass hK hD
        hAhead hrho hrate hgeom Cert htri hDelta hDelta1
        hradius hradiusCap hseries hneumann
    let SInner := cmp116SourcePhysicalLocalizedCoordinates Dict Z0
    let SOuter := cmp116SourcePhysicalLocalizedCoordinates Dict Z
    let Csource := Craw.withConditionedOuterCarrier SOuter
    (∀ sigma tau,
      CMP116Eq214ShiftedPolydisc nDelta Csource.deltaRadius sigma →
      CMP116Eq214CenteredPolydisc nY Csource.yRadius tau →
      ∀ x b,
      ‖Csource.toLocalFiniteGaussianData.toFiniteGaussianData.innerWeight
          sigma tau psi phi x b‖ ≤
        Real.exp (∑ i,
          Csource.r3RealSource sigma tau
            (restrictGlobal Csource.spectatorSupport psi)
            (restrictGlobal Csource.fluctuationSupport phi) x i * b i)) →
    (∀ sigma tau,
      CMP116Eq214ShiftedPolydisc nDelta Csource.deltaRadius sigma →
      CMP116Eq214CenteredPolydisc nY Csource.yRadius tau →
      ∀ᵐ b ∂matrixGaussianPi Csource.referenceRoot,
      (Csource.toLocalFiniteGaussianData.toFiniteGaussianData.interactionExponent
          sigma tau psi phi b).re +
        (gamma / 2) *
          (∑ bond ∈ P,
            ‖Csource.toLocalFiniteGaussianData.toFiniteGaussianData.bondField
              b bond‖ ^ 2) ≤
        -((b ⬝ᵥ Matrix.mulVec
          (-(alpha • cmp116Eq223CoordinateProjection SInner)) b) / 2) +
          residual) →
    CMP116Eq214NestedCauchyBoundaryBound nDelta nY
      Csource.deltaRadius Csource.yRadius
      (fun sigma tau =>
        Csource.toLocalFiniteGaussianData.toFiniteGaussianData.toAnalyticData.analyticIntegrand
          Y0 P sigma tau psi phi)
      (Real.exp
          (residual - gamma / 2 * Csource.threshold ^ 2 *
            (P.card : ℝ)) *
        ((Real.exp
            (cmp116SourceRestrictedUniformContourDeterminantCost
                M Nc Delta radius (1 + radius) rate Ahead rho
                ‖cmp116PhysicalEndomorphismComplexMatrix K‖ *
              (Z0.card : ℝ)) *
          cmp116Eq225LocalizedSourceEnergyPrefactor SInner
            Csource.referenceRoot alpha 0) *
          Real.exp
            (((cmp116SourceRestrictedUniformR1TraceCost
                  nDelta M Nc Delta radius (1 + radius) rate Ahead rho
                  (cmp116SourcePi4PhysicalComplexR1TraceMultiplierBound
                    K root hc hmass hK Z0 Delta
                      Ahead rho rate radius (1 + radius)) +
                2 *
                  |cmp116Eq225SourceCoefficient Csource.referenceRoot alpha *
                    cmp116SourcePi4PhysicalComplexR3SourceRate
                      K root Z0 Delta Ahead rho rate radius (1 + radius)| *
                  (SOuter.card : ℝ)) /
              (1 - qBound)) / 2))) := by
  dsimp only
  intro hinner hinteraction
  let Craw :=
    C.withSourcePi4RestrictedComplexGaussianOfPhysicalContour
      anchor contourCarrier hcarrier e Z0 K root
      hsourceRange hfiniteRange hc hmass hK hD
      hAhead hrho hrate hgeom Cert htri hDelta hDelta1
      hradius hradiusCap hseries hneumann
  let SInner := cmp116SourcePhysicalLocalizedCoordinates Dict Z0
  let SOuter := cmp116SourcePhysicalLocalizedCoordinates Dict Z
  let Csource := Craw.withConditionedOuterCarrier SOuter
  let sourceRate :=
    cmp116SourcePi4PhysicalComplexR3SourceRate
      K root Z0 Delta Ahead rho rate radius (1 + radius)
  let determinantBound :=
    Real.exp
      (cmp116SourceRestrictedUniformContourDeterminantCost
          M Nc Delta radius (1 + radius) rate Ahead rho
          ‖cmp116PhysicalEndomorphismComplexMatrix K‖ *
        (Z0.card : ℝ))
  let traceCost :=
    cmp116SourceRestrictedUniformR1TraceCost
      nDelta M Nc Delta radius (1 + radius) rate Ahead rho
      (cmp116SourcePi4PhysicalComplexR1TraceMultiplierBound
        K root hc hmass hK Z0 Delta
          Ahead rho rate radius (1 + radius))
  apply Csource.nestedCauchyBoundaryBound_of_conditionedOuterTraceInteractionEnergy_cutoff_onShiftedCenteredPolydiscs
    Y0 P psi phi SInner SOuter alpha sourceRate determinantBound gamma residual
    (fun sigma tau x =>
      Csource.r3RealSource sigma tau
        (restrictGlobal Csource.spectatorSupport psi)
        (restrictGlobal Csource.fluctuationSupport phi) x)
    halpha hrootSmall hq0 hq1
  · apply cmp116SourceRestrictedUniformR1TraceCost_nonneg
    · exact hradius
    · exact hAhead
    · exact hgeom
    · exact
        cmp116SourcePi4PhysicalComplexR1TraceMultiplierBound_nonneg
          K root hc hmass hK Z0 Delta hAhead hradius hgeom
            hneumann hneumannTranspose
  · intro sigma tau hsigma htau
    have hsigmaC :
        CMP116Eq214ShiftedPolydisc nDelta C.deltaRadius sigma := by
      simpa [Csource, Craw] using hsigma
    have hz : ∀ i, ‖sigma i‖ ≤ radius := by
      intro i
      have hi : ‖sigma i‖ ≤ 1 + C.deltaRadius i := by
        simpa using hsigmaC i
      exact hi.trans (hradiusCap i)
    have hcap : ∀ i, ‖1 + sigma i‖ ≤ 1 + radius := by
      intro i
      calc
        ‖1 + sigma i‖ ≤ 1 + ‖sigma i‖ := by
          simpa using norm_add_le (1 : ℂ) (sigma i)
        _ ≤ 1 + radius := by linarith [hz i]
    change
      ‖cmp116Eq214LogDeterminantDensity
          (cmp116PhysicalEndomorphismComplexMatrix K)
          (cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
            (R := R) anchor K hc hmass hK
              (cmp116SourceRestrictedShiftedCoupling
                contourCarrier e sigma))‖ ≤ determinantBound
    exact
      norm_cmp116SourceRestrictedContour_logDetDensity_le_exp_uniformCost_card
        anchor contourCarrier Z0 hcarrierZ0 e sigma K
        hsourceRange hfiniteRange hc hmass hK hD
        hAhead hrho hrate hgeom Cert htri hDelta hDelta1
        hradius (by linarith) hz hcap hseries hneumann
  · exact hgamma
  · simpa [Csource, Craw] using hthreshold
  · exact hinner
  · exact hinteraction
  · intro sigma tau hsigma htau x
    have hsigmaC :
        CMP116Eq214ShiftedPolydisc nDelta C.deltaRadius sigma := by
      simpa [Csource, Craw] using hsigma
    change
      Csource.r3RealSource sigma tau
          (restrictGlobal Csource.spectatorSupport psi)
          (restrictGlobal Csource.fluctuationSupport phi) x ⬝ᵥ
        Csource.r3RealSource sigma tau
          (restrictGlobal Csource.spectatorSupport psi)
          (restrictGlobal Csource.fluctuationSupport phi) x ≤
        sourceRate * (∑ i ∈ SOuter, x i ^ 2) + 0
    simpa [sourceRate, SOuter, Csource, Craw] using
      (C.dotProduct_sourcePi4RestrictedConditioned_r3RealSource_self_le_physical
        Dict anchor contourCarrier hcarrier e Z0 Z K root
        hsourceRange hfiniteRange hc hmass hK hD
        hAhead hrho hrate hgeom Cert htri hDelta hDelta1
        hradius hradiusCap hseries hneumann hneumannTranspose
        sigma hsigmaC tau
        (restrictGlobal C.spectatorSupport psi)
        (restrictGlobal C.fluctuationSupport phi) x)
  · intro sigma tau hsigma htau
    have hsigmaC :
        CMP116Eq214ShiftedPolydisc nDelta C.deltaRadius sigma := by
      simpa [Csource, Craw] using hsigma
    rw [Craw.withConditionedOuterCarrier_r1Matrix SOuter]
    rw [conditionedOuterProjection_transpose]
    have hraw :=
      cmp116SourceRestrictedR1_combinedBilateralRadius_le_physicalDefect
        anchor contourCarrier e sigma K root
        hsourceRange hfiniteRange hc hmass hK hD Z0
        hAhead hrho hrate hgeom Cert htri hDelta hDelta1
        hradius C.deltaRadius hradiusCap hsigmaC hseries
        hneumann hneumannTranspose
        (cmp116Eq225SourceCoefficient
          (cmp116PhysicalEndomorphismRealMatrix root) alpha * sourceRate)
    calc
      (‖conditionedOuterProjection SOuter *
            Craw.r1Matrix sigma tau
              (restrictGlobal Craw.spectatorSupport psi)
              (restrictGlobal Craw.fluctuationSupport phi) *
            conditionedOuterProjection SOuter‖ +
          ‖(conditionedOuterProjection SOuter *
            Craw.r1Matrix sigma tau
              (restrictGlobal Craw.spectatorSupport psi)
              (restrictGlobal Craw.fluctuationSupport phi) *
            conditionedOuterProjection SOuter).transpose‖) / 2 +
          2 *
            |cmp116Eq225SourceCoefficient Csource.referenceRoot alpha *
              sourceRate| ≤
        (‖Craw.r1Matrix sigma tau
              (restrictGlobal Craw.spectatorSupport psi)
              (restrictGlobal Craw.fluctuationSupport phi)‖ +
          ‖(Craw.r1Matrix sigma tau
              (restrictGlobal Craw.spectatorSupport psi)
              (restrictGlobal Craw.fluctuationSupport phi)).transpose‖) / 2 +
          2 *
            |cmp116Eq225SourceCoefficient Csource.referenceRoot alpha *
              sourceRate| := by
        gcongr
        · exact linfty_opNorm_conditionedOuterProjection_mul_mul_le SOuter _
        · exact
            linfty_opNorm_transpose_conditionedOuterProjection_mul_mul_le SOuter _
      _ ≤ qBound := by
        simpa [Craw, Csource, sourceRate] using hraw.trans hOuterSmall
  · intro sigma tau hsigma htau Qtest hQtest
    have hsigmaC :
        CMP116Eq214ShiftedPolydisc nDelta C.deltaRadius sigma := by
      simpa [Csource, Craw] using hsigma
    rw [Craw.withConditionedOuterCarrier_r1Matrix SOuter]
    rw [conditionedOuterProjection_transpose]
    apply norm_trace_conditionedOuterProjection_mul_mul_le_of
      SOuter
      (Craw.r1Matrix sigma tau
        (restrictGlobal Craw.spectatorSupport psi)
        (restrictGlobal Craw.fluctuationSupport phi))
      (by
        apply cmp116SourceRestrictedUniformR1TraceCost_nonneg
        · exact hradius
        · exact hAhead
        · exact hgeom
        · exact
            cmp116SourcePi4PhysicalComplexR1TraceMultiplierBound_nonneg
              K root hc hmass hK Z0 Delta hAhead hradius hgeom
                hneumann hneumannTranspose)
      ?_ Qtest hQtest
    intro Q hQ
    change
      ‖Matrix.trace
        (cmp116SourcePi4FullComplexR1Matrix
          (R := R) anchor K root hc hmass hK Z0
            (cmp116SourceRestrictedShiftedCoupling contourCarrier e sigma) *
          Q)‖ ≤ traceCost * ‖Q‖
    have hz : ∀ i, ‖sigma i‖ ≤ radius := by
      intro i
      have hi : ‖sigma i‖ ≤ 1 + C.deltaRadius i := by
        simpa using hsigmaC i
      exact hi.trans (hradiusCap i)
    have hcap : ∀ i, ‖1 + sigma i‖ ≤ 1 + radius := by
      intro i
      calc
        ‖1 + sigma i‖ ≤ 1 + ‖sigma i‖ := by
          simpa using norm_add_le (1 : ℂ) (sigma i)
        _ ≤ 1 + radius := by linarith [hz i]
    exact
      norm_trace_cmp116SourcePi4FullComplexR1Matrix_mul_le_uniform_physical
        anchor contourCarrier e sigma K root
        hsourceRange hfiniteRange hc hmass hK hD
        hAhead hrho Cert hrate hgeom htri hDelta hDelta1 Z0
        hradius (by linarith) hz hcap hseries hneumann
        hneumannTranspose Q hQ

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
