/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourceRestrictedConditionedPhysicalOuterResidualBoundary
import YangMills.RG.BalabanCMP116SourceRestrictedConditionedPhysicalOuterCardinality
import YangMills.RG.BalabanCMP116Eq220ConditionedResidualLedger
import YangMills.RG.BalabanCMP116Eq226SigmaCauchy
import YangMills.RG.BalabanCMP116Eq226GenericResidualLedger

/-!
# Source-specific conditioned boundary through equation (2.26)

This is the source-faithful equation-(2.26) endpoint.  The inner covariance,
contour determinant, and residual domains use `Z₀`; the outer product
Gaussian and the final polymer volume use `Z`.  The physical `R3` source rate
is generated internally, and no pointwise source-energy hypothesis occurs.
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
/-- The conditioned physical contour, the integrated outer boundary on `Z`,
and the rooted equation-(1.36) ledger on `Z₀` produce the literal
equation-(2.26) term weight with volume `|Z|`. -/
theorem
    norm_term_le_eq226SourceTermWeight_of_sourcePi4ConditionedPhysicalOuterResidualLedger
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
    (conditionedCovariance :
      Matrix
        (PhysicalGaugeCoordIndex 4 (M * (2 * Q)) Nc)
        (PhysicalGaugeCoordIndex 4 (M * (2 * Q)) Nc) ℝ)
    (hconditionedRoot :
      MatrixConditionedGaussianRootCertificate
        conditionedCovariance
        (cmp116PhysicalEndomorphismRealMatrix root)
        (cmp116SourcePhysicalLocalizedCoordinates Dict Z0))
    (hnondegenerate :
      MatrixConditionedGaussianCovarianceLowerCertificate
        conditionedCovariance
        (cmp116SourcePhysicalLocalizedCoordinates Dict Z0))
    (alpha gamma : ℝ)
    {qBound : ℝ} (hq0 : 0 ≤ qBound) (hq1 : qBound < 1)
    {E0 epsilon1 C1 alpha4 : ℝ} {q : ℕ}
    {C2 kappa1 delta kappa gk : ℝ}
    (domainMetric : Fin nY → ℕ)
    (domainSupport : Fin nY → Finset (FinBox 4 (2 * Q)))
    (residualWeight : Fin nY → ℝ)
    (gapL gapCard : ℕ)
    (rootBound Calpha : ℝ)
    (hDeltaRadius :
      (C.withSourcePi4RestrictedComplexGaussianOfPhysicalContour
        anchor contourCarrier hcarrier e Z0 K root
        hsourceRange hfiniteRange hc hmass hK hD
        hAhead hrho hrate hgeom Cert htri hDelta hDelta1
        hradius hradiusCap hseries hneumann).deltaRadius =
          fun _ => cmp116Eq214SigmaCauchyRadius kappa1)
    (hnormalizedGap :
      ((((gapL * M : ℕ) : ℝ) ^ 4)⁻¹ * (gapCard : ℝ)) =
        (nDelta : ℝ))
    (hYRadius :
      (C.withSourcePi4RestrictedComplexGaussianOfPhysicalContour
        anchor contourCarrier hcarrier e Z0 K root
        hsourceRange hfiniteRange hc hmass hK hD
        hAhead hrho hrate hgeom Cert htri hDelta hDelta1
        hradius hradiusCap hseries hneumann).yRadius =
          fun Y =>
            cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
              C2 kappa1 delta kappa (domainMetric Y : ℝ))
    (hE0 : 0 < E0) (hepsilon1 : 0 < epsilon1)
    (hC1 : 0 < C1) (halpha4 : 0 < alpha4) (hM : 1 ≤ M)
    (hgk : gk ≠ 0)
    (hthresholdEq :
      (C.withSourcePi4RestrictedComplexGaussianOfPhysicalContour
        anchor contourCarrier hcarrier e Z0 K root
        hsourceRange hfiniteRange hc hmass hK hD
        hAhead hrho hrate hgeom Cert htri hDelta hDelta1
        hradius hradiusCap hseries hneumann).threshold =
          epsilon1 / gk)
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
    (hthresholdNonneg :
      0 ≤
        (C.withSourcePi4RestrictedComplexGaussianOfPhysicalContour
          anchor contourCarrier hcarrier e Z0 K root
          hsourceRange hfiniteRange hc hmass hK hD
          hAhead hrho hrate hgeom Cert htri hDelta hDelta1
          hradius hradiusCap hseries hneumann).threshold)
    (hOuterSmall :
      2 *
        (cmp116SourcePi4PhysicalComplexR1DefectBilateralBudget
            K root hc hmass hK Z0 Delta Ahead rho rate radius (1 + radius) +
          |cmp116Eq225SourceCoefficient
              (cmp116PhysicalEndomorphismRealMatrix root) alpha *
            cmp116SourcePi4PhysicalComplexR3SourceRate
              K root Z0 Delta Ahead rho rate radius (1 + radius)|) ≤
        qBound)
    (hinteraction :
      let Craw :=
        C.withSourcePi4RestrictedComplexGaussianOfPhysicalContour
          anchor contourCarrier hcarrier e Z0 K root
          hsourceRange hfiniteRange hc hmass hK hD
          hAhead hrho hrate hgeom Cert htri hDelta hDelta1
          hradius hradiusCap hseries hneumann
      let SInner := cmp116SourcePhysicalLocalizedCoordinates Dict Z0
      let SOuter := cmp116SourcePhysicalLocalizedCoordinates Dict Z
      let Csource := Craw.withConditionedOuterCarrier SOuter
      ∀ sigma tau,
        CMP116Eq214ShiftedPolydisc nDelta Csource.deltaRadius sigma →
        CMP116Eq214CenteredPolydisc nY Csource.yRadius tau →
        ∀ᵐ b ∂matrixGaussianPi Csource.referenceRoot,
        Csource.toLocalFiniteGaussianData.toFiniteGaussianData.toAnalyticData.cutoffFactor
            Y0 P b ≠ 0 →
        (Csource.toLocalFiniteGaussianData.toFiniteGaussianData.interactionExponent
            sigma tau psi phi b).re +
          (gamma / 2) *
            (∑ bond ∈ P,
              ‖Csource.toLocalFiniteGaussianData.toFiniteGaussianData.bondField
                b bond‖ ^ 2) ≤
          -((b ⬝ᵥ Matrix.mulVec
            (-(alpha • cmp116Eq223CoordinateProjection SInner)) b) / 2) +
            ∑ Y : Fin nY,
              residualWeight Y)
    (hweight : ∀ Y : Fin nY, 0 ≤ residualWeight Y)
    (hne : ∀ Y : Fin nY, (domainSupport Y).Nonempty)
    (hsub : ∀ Y : Fin nY, domainSupport Y ⊆ Z0)
    (hrootNonneg : 0 ≤ rootBound)
    (hroot : ∀ i ∈ Z0,
      ∑ Y ∈ (Finset.univ.filter fun Y : Fin nY =>
          i ∈ domainSupport Y),
        residualWeight Y ≤ rootBound)
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
    let Craw :=
      C.withSourcePi4RestrictedComplexGaussianOfPhysicalContour
        anchor contourCarrier hcarrier e Z0 K root
        hsourceRange hfiniteRange hc hmass hK hD
        hAhead hrho hrate hgeom Cert htri hDelta hDelta1
        hradius hradiusCap hseries hneumann
    let SOuter := cmp116SourcePhysicalLocalizedCoordinates Dict Z
    let Csource := Craw.withConditionedOuterCarrier SOuter
    ‖Csource.toLocalFiniteGaussianData.toFiniteGaussianData.toAnalyticData.term
        Y0 P psi phi‖ ≤
      cmp116Eq226SourceTermWeight E0 epsilon1 C1 alpha4 M q
        C2 kappa1 delta kappa gamma gk gapL gapCard
        Calpha alpha Z.card domainMetric Finset.univ P := by
  dsimp only
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
  let residualSum :=
    ∑ Y : Fin nY, residualWeight Y
  let determinantCost :=
    cmp116SourceRestrictedUniformContourDeterminantCost
      M Nc Delta radius (1 + radius) rate Ahead rho
        ‖cmp116PhysicalEndomorphismComplexMatrix K‖
  let outerBoundary :=
    (Real.exp (determinantCost * (Z0.card : ℝ)) *
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
                sourceRate| *
              (SOuter.card : ℝ)) /
          (1 - qBound)) / 2)
  let outerCost :=
    cmp116SourceRestrictedConditionedPhysicalOuterPerCarrierCost
      K root hc hmass hK Z0 Delta radius rate Ahead rho
        alpha sourceRate qBound determinantCost
  let boundaryMajorant :=
    Real.exp
        (residualSum - gamma / 2 * Csource.threshold ^ 2 *
          (P.card : ℝ)) *
      outerBoundary
  have hboundary :
      CMP116Eq214NestedCauchyBoundaryBound nDelta nY
        Csource.deltaRadius Csource.yRadius
        (fun sigma tau =>
          Csource.toLocalFiniteGaussianData.toFiniteGaussianData.toAnalyticData.analyticIntegrand
            Y0 P sigma tau psi phi)
        boundaryMajorant := by
    dsimp [boundaryMajorant, outerBoundary, determinantCost, residualSum,
      sourceRate, SInner, SOuter, Csource, Craw]
    exact
      C.nestedCauchyBoundaryBound_of_sourcePi4ConditionedPhysicalOuterResidual
        Dict anchor contourCarrier Z0 Z hcarrier hcarrierZ0 e K root
        hsourceRange hfiniteRange hc hmass hK hD
        hAhead hrho hrate hgeom Cert htri hDelta hDelta1
        hradius hradiusCap hseries hneumann hneumannTranspose
        Y0 P psi phi conditionedCovariance hconditionedRoot hnondegenerate
        alpha gamma
        (∑ Y : Fin nY, residualWeight Y)
        halpha hrootSmall hgamma hthresholdNonneg hq0 hq1 hOuterSmall
        (by
          intro sigma tau hsigma htau x b
          let Craw :=
            C.withSourcePi4RestrictedComplexGaussianOfPhysicalContour
              anchor contourCarrier hcarrier e Z0 K root
              hsourceRange hfiniteRange hc hmass hK hD
              hAhead hrho hrate hgeom Cert htri hDelta hDelta1
              hradius hradiusCap hseries hneumann
          let Csource :=
            Craw.withConditionedOuterCarrier
              (cmp116SourcePhysicalLocalizedCoordinates Dict Z)
          exact
            (Csource.norm_innerWeight_eq_exp_sum_r3RealSource
              sigma tau
              (restrictGlobal Csource.spectatorSupport psi)
              (restrictGlobal Csource.fluctuationSupport phi) x b).le)
        (by
          dsimp only at hinteraction
          exact hinteraction)
  have houterBoundaryNonneg : 0 ≤ outerBoundary := by
    dsimp [outerBoundary]
    apply mul_nonneg
    · apply mul_nonneg (Real.exp_nonneg _)
      unfold cmp116Eq225LocalizedSourceEnergyPrefactor
      positivity
    · exact Real.exp_nonneg _
  have hterm :
      ‖Csource.toLocalFiniteGaussianData.toFiniteGaussianData.toAnalyticData.term
          Y0 P psi phi‖ ≤
        (boundaryMajorant *
          cmp116Eq226DomainProduct E0 epsilon1 C1 alpha4 M q
            C2 kappa1 delta kappa domainMetric Finset.univ) *
          cmp116Eq226GapFactor kappa1 gapL M gapCard := by
    apply
      Csource.toLocalFiniteGaussianData.toFiniteGaussianData.toAnalyticData
        |>.norm_term_le_eq226DomainGap_of_boundary
          Y0 P psi phi domainMetric gapL gapCard boundaryMajorant
    · simpa [Csource, Craw] using hDeltaRadius
    · exact hnormalizedGap
    · simpa [Csource, Craw] using hYRadius
    · exact hE0
    · exact hepsilon1
    · exact hC1
    · exact halpha4
    · exact hM
    · dsimp [boundaryMajorant]
      exact mul_nonneg (Real.exp_nonneg _) houterBoundaryNonneg
    · exact hboundary
  have houterCard :
      outerBoundary ≤ Real.exp (outerCost * (Z.card : ℝ)) := by
    dsimp [outerBoundary, outerCost, determinantCost, sourceRate,
      SInner, SOuter,
      Csource, Craw]
    exact
      cmp116SourceRestrictedConditionedPhysicalOuterBoundary_le_exp_card
        contourCarrier Z0 Z e hcarrierZ0 hZ0Z Dict K root hc hmass hK
        hradius hAhead hgeom hneumann hneumannTranspose
        halpha hrootSmall hq1
  refine hterm.trans ?_
  dsimp [boundaryMajorant]
  have hledger :=
    cmp116Eq226_boundaryProduct_le_sourceTermWeight_of_conditionedGenericResidualLedger_outerCard
      (D := (Finset.univ : Finset (Fin nY))) (P := P)
      (Z0 := Z0) (Z := Z) hZ0Z
      domainSupport residualWeight domainMetric
      (M := M) (q := q) (C2 := C2) (kappa1 := kappa1)
      (delta := delta) (kappa := kappa) (gamma2 := gamma)
      (gk := gk) (threshold := Csource.threshold)
      (L := gapL) (gapCard := gapCard)
      (rootBound := rootBound) (baseRate := 0)
      (outerCost := outerCost) (Calpha5 := Calpha) (alpha5 := alpha)
      (outerBound := outerBoundary)
      hE0.le hepsilon1.le hC1.le halpha4.le hgk
      (by simpa [Csource, Craw] using hthresholdEq)
      houterCard
      (by
        intro Y _
        exact hweight Y)
      (by
        intro Y _
        exact hne Y)
      (by
        intro Y _
        exact hsub Y)
      hrootNonneg hroot
      (by
        dsimp [outerCost, determinantCost, sourceRate]
        simpa using hvolumeBudget)
  rw [mul_comm
    (Real.exp
      (residualSum - gamma / 2 * Csource.threshold ^ 2 *
        (P.card : ℝ)))
    outerBoundary]
  simpa [residualSum] using hledger

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
