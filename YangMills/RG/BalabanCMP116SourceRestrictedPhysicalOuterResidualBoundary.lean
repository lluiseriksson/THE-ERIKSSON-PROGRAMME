/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq225OuterTraceInteractionResidual
import YangMills.RG.BalabanCMP116SourceRestrictedPhysicalOuterBoundary

/-!
# Physical restricted outer boundary with the source residual

This is the source-specific residual-preserving counterpart of the physical
outer reduction.  The only analytic premises describe the literal inner
weight, interaction exponent, and source energy.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

namespace CMP116Eq214PhysicalContourDensity

set_option maxHeartbeats 12000000 in
/-- Literal residual-preserving nested boundary for the restricted physical
source contour. -/
theorem nestedCauchyBoundaryBound_of_sourcePi4PhysicalOuterResidual
    {nDelta nY M Q Nc R Delta : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    {Site E : Type*} {Psi Phi : Site → Type*} [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond 4 (M * (2 * Q))) Site Psi Phi E (Nc ^ 2 - 1))
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
    (S : Finset
      (PhysicalBond 4 (M * (2 * Q)) × Fin (Nc ^ 2 - 1)))
    (alpha sourceRate gamma residual : ℝ)
    (r : (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      CMP116Eq214GaussianCoordinate
        (PhysicalBond 4 (M * (2 * Q))) (Nc ^ 2 - 1) →
      PhysicalBond 4 (M * (2 * Q)) × Fin (Nc ^ 2 - 1) → ℝ)
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
            sourceRate|) ≤ qBound) :
    let Csource :=
      C.withSourcePi4RestrictedComplexGaussianOfPhysicalContour
        anchor contourCarrier hcarrier e Z0 K root
        hsourceRange hfiniteRange hc hmass hK hD
        hAhead hrho hrate hgeom Cert htri hDelta hDelta1
        hradius hradiusCap hseries hneumann
    (∀ sigma tau,
      CMP116Eq214ShiftedPolydisc nDelta Csource.deltaRadius sigma →
      CMP116Eq214ShiftedPolydisc nY Csource.yRadius tau →
      ∀ x b,
      ‖Csource.toLocalFiniteGaussianData.toFiniteGaussianData.innerWeight
          sigma tau psi phi x b‖ ≤
        Real.exp (∑ i, r sigma tau x i * b i)) →
    (∀ sigma tau,
      CMP116Eq214ShiftedPolydisc nDelta Csource.deltaRadius sigma →
      CMP116Eq214ShiftedPolydisc nY Csource.yRadius tau →
      ∀ b,
      (Csource.toLocalFiniteGaussianData.toFiniteGaussianData.interactionExponent
          sigma tau psi phi b).re +
        (gamma / 2) *
          (∑ bond ∈ P,
            ‖Csource.toLocalFiniteGaussianData.toFiniteGaussianData.bondField
              b bond‖ ^ 2) ≤
        -((b ⬝ᵥ Matrix.mulVec
          (-(alpha • cmp116Eq223CoordinateProjection S)) b) / 2) +
          residual) →
    (∀ sigma tau,
      CMP116Eq214ShiftedPolydisc nDelta Csource.deltaRadius sigma →
      CMP116Eq214ShiftedPolydisc nY Csource.yRadius tau →
      ∀ x,
      (r sigma tau x) ⬝ᵥ (r sigma tau x) ≤
        sourceRate * (∑ i ∈ S, x i ^ 2) + 0) →
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
              (1 - qBound)) / 2))) := by
  dsimp only
  intro hinner hinteraction hsource
  apply
    (C.withSourcePi4RestrictedComplexGaussianOfPhysicalContour
      anchor contourCarrier hcarrier e Z0 K root
      hsourceRange hfiniteRange hc hmass hK hD
      hAhead hrho hrate hgeom Cert htri hDelta hDelta1
      hradius hradiusCap hseries hneumann
    ).nestedCauchyBoundaryBound_of_outerTraceInteractionEnergy_cutoff_onPolydiscs
      Y0 P psi phi S alpha sourceRate
      (Real.exp
        (cmp116SourceRestrictedUniformContourDeterminantCost
            M Nc Delta radius (1 + radius) rate Ahead rho
            ‖cmp116PhysicalEndomorphismComplexMatrix K‖ *
          (Z0.card : ℝ)))
      gamma residual r halpha hrootSmall hq0 hq1
  · apply cmp116SourceRestrictedUniformR1TraceCost_nonneg
    · exact hradius
    · exact hAhead
    · exact hgeom
    · exact
        cmp116SourcePi4PhysicalComplexR1TraceMultiplierBound_nonneg
          K root hc hmass hK Z0 Delta hAhead hradius hgeom
            hneumann hneumannTranspose
  · intro sigma tau hsigma htau
    have hz : ∀ i, ‖sigma i‖ ≤ radius := by
      intro i
      have hi : ‖sigma i‖ ≤ 1 + C.deltaRadius i := by
        simpa using hsigma i
      exact hi.trans (hradiusCap i)
    have hcap : ∀ i, ‖1 + sigma i‖ ≤ 1 + radius := by
      intro i
      calc
        ‖1 + sigma i‖ ≤ ‖(1 : ℂ)‖ + ‖sigma i‖ := norm_add_le _ _
        _ ≤ 1 + radius := by simpa using add_le_add (le_refl 1) (hz i)
    change
      ‖cmp116Eq214LogDeterminantDensity
          (cmp116PhysicalEndomorphismComplexMatrix K)
          (cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
            (R := R) anchor K hc hmass hK
              (cmp116SourceRestrictedShiftedCoupling
                contourCarrier e sigma))‖ ≤ _
    exact
      norm_cmp116SourceRestrictedContour_logDetDensity_le_exp_uniformCost_card
        anchor contourCarrier Z0 hcarrierZ0 e sigma K
        hsourceRange hfiniteRange hc hmass hK hD
        hAhead hrho hrate hgeom Cert htri hDelta hDelta1
        hradius (by linarith) hz hcap hseries hneumann
  · exact hgamma
  · simpa using hthreshold
  · exact hinner
  · exact hinteraction
  · exact hsource
  · intro sigma tau hsigma htau
    change
      (‖cmp116SourcePi4FullComplexR1Matrix
          (R := R) anchor K root hc hmass hK Z0
            (cmp116SourceRestrictedShiftedCoupling contourCarrier e sigma)‖ +
        ‖(cmp116SourcePi4FullComplexR1Matrix
          (R := R) anchor K root hc hmass hK Z0
            (cmp116SourceRestrictedShiftedCoupling
              contourCarrier e sigma)).transpose‖) / 2 +
        2 *
          |cmp116Eq225SourceCoefficient
              (cmp116PhysicalEndomorphismRealMatrix root) alpha *
            sourceRate| ≤ qBound
    exact
      (cmp116SourceRestrictedR1_combinedBilateralRadius_le_physicalDefect
        anchor contourCarrier e sigma K root
        hsourceRange hfiniteRange hc hmass hK hD Z0
        hAhead hrho hrate hgeom Cert htri hDelta hDelta1
        hradius C.deltaRadius hradiusCap hsigma hseries
        hneumann hneumannTranspose
        (cmp116Eq225SourceCoefficient
          (cmp116PhysicalEndomorphismRealMatrix root) alpha *
            sourceRate)).trans hOuterSmall
  · intro sigma tau hsigma htau Ptest hPt
    have hz : ∀ i, ‖sigma i‖ ≤ radius := by
      intro i
      have hi : ‖sigma i‖ ≤ 1 + C.deltaRadius i := by
        simpa using hsigma i
      exact hi.trans (hradiusCap i)
    have hcap : ∀ i, ‖1 + sigma i‖ ≤ 1 + radius := by
      intro i
      calc
        ‖1 + sigma i‖ ≤ ‖(1 : ℂ)‖ + ‖sigma i‖ := norm_add_le _ _
        _ ≤ 1 + radius := by simpa using add_le_add (le_refl 1) (hz i)
    change
      ‖Matrix.trace
        (cmp116SourcePi4FullComplexR1Matrix
          (R := R) anchor K root hc hmass hK Z0
            (cmp116SourceRestrictedShiftedCoupling contourCarrier e sigma) *
          Ptest)‖ ≤
        cmp116SourceRestrictedUniformR1TraceCost
          nDelta M Nc Delta radius (1 + radius) rate Ahead rho
            (cmp116SourcePi4PhysicalComplexR1TraceMultiplierBound
              K root hc hmass hK Z0 Delta
                Ahead rho rate radius (1 + radius)) *
          ‖Ptest‖
    exact
      norm_trace_cmp116SourcePi4FullComplexR1Matrix_mul_le_uniform_physical
        anchor contourCarrier e sigma K root
        hsourceRange hfiniteRange hc hmass hK hD
        hAhead hrho Cert hrate hgeom htri hDelta hDelta1 Z0
        hradius (by linarith) hz hcap hseries hneumann
        hneumannTranspose Ptest hPt

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
