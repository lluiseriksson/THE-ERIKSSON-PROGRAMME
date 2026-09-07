/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourceRestrictedPhysicalOuterResidualBoundary
import YangMills.RG.BalabanCMP116SourceRestrictedPhysicalOuterCardinality
import YangMills.RG.BalabanCMP116Eq226SigmaCauchy
import YangMills.RG.BalabanCMP116Eq220ResidualLedger
import YangMills.RG.BalabanCMP116Eq214PhysicalContourR3Source

/-!
# Source-specific physical boundary through equation (2.26)

The cutoff index `P` in this module is literally a finite family of physical
bonds.  The localization domains and `Z0` remain block-domain data.  Thus the
equation-(2.22) cutoff cardinality and the equation-(2.26) `P` factor are the
same cardinality; no cube--bond identification is used.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

namespace CMP116Eq214PhysicalContourDensity

set_option maxHeartbeats 16000000 in
/-- The restricted physical contour, its integrated outer boundary, and the
rooted equation-(1.36) residual ledger produce the literal equation-(2.26)
term weight.  No complete-term majorant is an input. -/
theorem norm_term_le_eq226SourceTermWeight_of_sourcePi4PhysicalOuterResidualLedger
    {nDelta nY M Q Nc R Delta L lieDim : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero L] [NeZero lieDim]
    {Site E : Type*} {Psi Phi : Site → Type*} [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond 4 (M * (2 * Q))) Site Psi Phi E (Nc ^ 2 - 1))
    (Dict : PhysicalGaugeCMP116Dictionary
      4 (M * (2 * Q)) Nc 4 L lieDim)
    (anchor : FinBox 4 Q)
    (contourCarrier Z0 : Finset (FinBox 4 (2 * Q)))
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
    (alpha sourceRate gamma : ℝ)
    {qBound : ℝ} (hq0 : 0 ≤ qBound) (hq1 : qBound < 1)
    {E0 epsilon1 C1 alpha4 : ℝ} {q : ℕ}
    {C2 kappa1 delta kappa gk : ℝ}
    (domainMetric : Fin nY → ℕ)
    (domainSupport : Fin nY → Finset (FinBox 4 (2 * Q)))
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
            sourceRate|) ≤ qBound)
    (hinteraction : ∀ sigma tau,
      CMP116Eq214ShiftedPolydisc nDelta
        (C.withSourcePi4RestrictedComplexGaussianOfPhysicalContour
          anchor contourCarrier hcarrier e Z0 K root
          hsourceRange hfiniteRange hc hmass hK hD
          hAhead hrho hrate hgeom Cert htri hDelta hDelta1
          hradius hradiusCap hseries hneumann).deltaRadius sigma →
      CMP116Eq214ShiftedPolydisc nY
        (C.withSourcePi4RestrictedComplexGaussianOfPhysicalContour
          anchor contourCarrier hcarrier e Z0 K root
          hsourceRange hfiniteRange hc hmass hK hD
          hAhead hrho hrate hgeom Cert htri hDelta hDelta1
          hradius hradiusCap hseries hneumann).yRadius tau →
      ∀ b,
      ((C.withSourcePi4RestrictedComplexGaussianOfPhysicalContour
          anchor contourCarrier hcarrier e Z0 K root
          hsourceRange hfiniteRange hc hmass hK hD
          hAhead hrho hrate hgeom Cert htri hDelta hDelta1
          hradius hradiusCap hseries hneumann
        ).toLocalFiniteGaussianData.toFiniteGaussianData.interactionExponent
          sigma tau psi phi b).re +
        (gamma / 2) *
          (∑ bond ∈ P,
            ‖(C.withSourcePi4RestrictedComplexGaussianOfPhysicalContour
              anchor contourCarrier hcarrier e Z0 K root
              hsourceRange hfiniteRange hc hmass hK hD
              hAhead hrho hrate hgeom Cert htri hDelta hDelta1
              hradius hradiusCap hseries hneumann
            ).toLocalFiniteGaussianData.toFiniteGaussianData.bondField
              b bond‖ ^ 2) ≤
        -((b ⬝ᵥ Matrix.mulVec
          (-(alpha • cmp116Eq223CoordinateProjection
            (cmp116SourcePhysicalLocalizedCoordinates Dict Z0))) b) / 2) +
          ∑ Y : Fin nY,
            cmp116Eq220ResidualDomainWeight alpha4 delta kappa
              (domainMetric Y : ℝ))
    (hsource : ∀ sigma tau,
      CMP116Eq214ShiftedPolydisc nDelta
        (C.withSourcePi4RestrictedComplexGaussianOfPhysicalContour
          anchor contourCarrier hcarrier e Z0 K root
          hsourceRange hfiniteRange hc hmass hK hD
          hAhead hrho hrate hgeom Cert htri hDelta hDelta1
          hradius hradiusCap hseries hneumann).deltaRadius sigma →
      CMP116Eq214ShiftedPolydisc nY
        (C.withSourcePi4RestrictedComplexGaussianOfPhysicalContour
          anchor contourCarrier hcarrier e Z0 K root
          hsourceRange hfiniteRange hc hmass hK hD
          hAhead hrho hrate hgeom Cert htri hDelta hDelta1
          hradius hradiusCap hseries hneumann).yRadius tau →
      ∀ x,
      let Csource :=
        C.withSourcePi4RestrictedComplexGaussianOfPhysicalContour
          anchor contourCarrier hcarrier e Z0 K root
          hsourceRange hfiniteRange hc hmass hK hD
          hAhead hrho hrate hgeom Cert htri hDelta hDelta1
          hradius hradiusCap hseries hneumann
      Csource.r3RealSource sigma tau
          (restrictGlobal Csource.spectatorSupport psi)
          (restrictGlobal Csource.fluctuationSupport phi) x ⬝ᵥ
        Csource.r3RealSource sigma tau
          (restrictGlobal Csource.spectatorSupport psi)
          (restrictGlobal Csource.fluctuationSupport phi) x ≤
        sourceRate *
          (∑ i ∈ cmp116SourcePhysicalLocalizedCoordinates Dict Z0,
            x i ^ 2) + 0)
    (hne : ∀ Y : Fin nY, (domainSupport Y).Nonempty)
    (hsub : ∀ Y : Fin nY, domainSupport Y ⊆ Z0)
    (hroot : ∀ i ∈ Z0,
      ∑ Y ∈ (Finset.univ.filter fun Y : Fin nY =>
          i ∈ domainSupport Y),
        cmp116Eq220ResidualDomainWeight alpha4 delta kappa
          (domainMetric Y : ℝ) ≤ rootBound)
    (hvolumeBudget :
      rootBound +
          cmp116SourceRestrictedPhysicalOuterPerCarrierCost
            K root hc hmass hK Z0 Delta radius rate Ahead rho
              alpha sourceRate qBound
              (cmp116SourceRestrictedUniformContourDeterminantCost
                M Nc Delta radius (1 + radius) rate Ahead rho
                  ‖cmp116PhysicalEndomorphismComplexMatrix K‖) ≤
        Calpha * alpha) :
    let Csource :=
      C.withSourcePi4RestrictedComplexGaussianOfPhysicalContour
        anchor contourCarrier hcarrier e Z0 K root
        hsourceRange hfiniteRange hc hmass hK hD
        hAhead hrho hrate hgeom Cert htri hDelta hDelta1
        hradius hradiusCap hseries hneumann
    ‖Csource.toLocalFiniteGaussianData.toFiniteGaussianData.toAnalyticData.term
        Y0 P psi phi‖ ≤
      cmp116Eq226SourceTermWeight E0 epsilon1 C1 alpha4 M q
        C2 kappa1 delta kappa gamma gk gapL gapCard
        Calpha alpha Z0.card domainMetric Finset.univ P := by
  dsimp only
  let Csource :=
    C.withSourcePi4RestrictedComplexGaussianOfPhysicalContour
      anchor contourCarrier hcarrier e Z0 K root
      hsourceRange hfiniteRange hc hmass hK hD
      hAhead hrho hrate hgeom Cert htri hDelta hDelta1
      hradius hradiusCap hseries hneumann
  let S := cmp116SourcePhysicalLocalizedCoordinates Dict Z0
  let residualSum :=
    ∑ Y : Fin nY,
      cmp116Eq220ResidualDomainWeight alpha4 delta kappa
        (domainMetric Y : ℝ)
  let determinantCost :=
    cmp116SourceRestrictedUniformContourDeterminantCost
      M Nc Delta radius (1 + radius) rate Ahead rho
        ‖cmp116PhysicalEndomorphismComplexMatrix K‖
  let outerBoundary :=
    (Real.exp (determinantCost * (Z0.card : ℝ)) *
        cmp116Eq225LocalizedSourceEnergyPrefactor S
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
              (S.card : ℝ)) /
          (1 - qBound)) / 2)
  let outerCost :=
    cmp116SourceRestrictedPhysicalOuterPerCarrierCost
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
      S, Csource]
    exact
      C.nestedCauchyBoundaryBound_of_sourcePi4PhysicalOuterResidual
        anchor contourCarrier Z0 hcarrier hcarrierZ0 e K root
        hsourceRange hfiniteRange hc hmass hK hD
        hAhead hrho hrate hgeom Cert htri hDelta hDelta1
        hradius hradiusCap hseries hneumann hneumannTranspose
        Y0 P psi phi
        (cmp116SourcePhysicalLocalizedCoordinates Dict Z0)
        alpha sourceRate gamma
        (∑ Y : Fin nY,
          cmp116Eq220ResidualDomainWeight alpha4 delta kappa
            (domainMetric Y : ℝ))
        (fun sigma tau x =>
          Csource.r3RealSource sigma tau
            (restrictGlobal Csource.spectatorSupport psi)
            (restrictGlobal Csource.fluctuationSupport phi) x)
        halpha hrootSmall hgamma hthresholdNonneg hq0 hq1 hOuterSmall
        (by
          intro sigma tau hsigma htau x b
          exact
            (Csource.norm_innerWeight_eq_exp_sum_r3RealSource
              sigma tau
              (restrictGlobal Csource.spectatorSupport psi)
              (restrictGlobal Csource.fluctuationSupport phi) x b).le)
        hinteraction
        (by
          intro sigma tau hsigma htau x
          simpa using hsource sigma tau hsigma htau x)
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
    · exact hDeltaRadius
    · exact hnormalizedGap
    · exact hYRadius
    · exact hE0
    · exact hepsilon1
    · exact hC1
    · exact halpha4
    · exact hM
    · dsimp [boundaryMajorant]
      exact mul_nonneg (Real.exp_nonneg _) houterBoundaryNonneg
    · exact hboundary
  have houterCard :
      outerBoundary ≤ Real.exp (outerCost * (Z0.card : ℝ)) := by
    dsimp [outerBoundary, outerCost, determinantCost, S, Csource]
    exact
      cmp116SourceRestrictedPhysicalOuterBoundary_le_exp_card
        contourCarrier Z0 e hcarrierZ0 Dict K root hc hmass hK
        hradius hAhead hgeom hneumann hneumannTranspose
        halpha hrootSmall hq1
  refine hterm.trans ?_
  dsimp [boundaryMajorant]
  have hledger :=
    cmp116Eq226_boundaryProduct_le_sourceTermWeight_of_residualLedger_outerCard
      (D := (Finset.univ : Finset (Fin nY))) (P := P) (Z0 := Z0)
      domainSupport (fun Y => (domainMetric Y : ℝ)) domainMetric
      (M := M) (q := q) (C2 := C2) (kappa1 := kappa1)
      (delta := delta) (kappa := kappa) (gamma2 := gamma)
      (gk := gk) (threshold := Csource.threshold)
      (L := gapL) (gapCard := gapCard)
      (rootBound := rootBound) (baseRate := 0)
      (outerCost := outerCost) (Calpha5 := Calpha) (alpha5 := alpha)
      (outerBound := outerBoundary)
      hE0.le hepsilon1.le hC1.le halpha4.le hgk hthresholdEq
      houterCard
      (by
        intro Y _
        exact hne Y)
      (by
        intro Y _
        exact hsub Y)
      hroot
      (by
        dsimp [outerCost, determinantCost]
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
