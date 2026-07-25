/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourceCenteredPhysicalAEInteraction
import YangMills.RG.BalabanCMP116SourceRestrictedPhysicalAEInteractionBoundary

/-!
# Conditioned physical interaction on centered source contours

This is the centered-source counterpart of the older shifted-polydisc
interaction producer.  It constructs the restricted physical `R2` bound,
consumes literal `(1.43)` and `(1.36)` through the radial Taylor operator,
and finally transports the result to the conditioned outer carrier.
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

set_option maxHeartbeats 8000000 in
/-- The source-faithful centered potential and the physical restricted `R2`
construction produce the AE interaction boundary on the conditioned outer
carrier. -/
theorem
    ae_interactionBoundary_of_sourcePi4ConditionedCenteredPhysicalPotential
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
    (E0 epsilon1 C1 alpha4 C3 C2 kappa1 delta kappa rowSum threshold :
      ℝ)
    (P : Finset (PhysicalBond 4 (M * (2 * Q))))
    (psi : ∀ s, Psi s) (phi : ∀ s, Phi s)
    (conditionedCovariance :
      Matrix
        (PhysicalGaugeCoordIndex 4 (M * (2 * Q)) Nc)
        (PhysicalGaugeCoordIndex 4 (M * (2 * Q)) Nc) ℝ)
    (hroot :
      MatrixConditionedGaussianRootCertificate
        conditionedCovariance
        (cmp116PhysicalEndomorphismRealMatrix root)
        (cmp116SourcePhysicalLocalizedCoordinates Dict Z0))
    (hE0 : 0 < E0) (hepsilon1 : 0 < epsilon1)
    (hC1 : 0 < C1) (halpha4 : 0 < alpha4)
    (hC3 : 0 ≤ C3) (hC3upper : C3 ≤ E0 * C1)
    (hM : 1 ≤ M) (hq : 8 ≤ q) (hkappa1 : 1 < kappa1)
    (hkappa :
      (1 - 3 * delta) * kappa ≤ (1 / 8 : ℝ) * (kappa1 - 1))
    (hdomainDist : ∀ y : Fin nY, 0 ≤ (domainMetric y : ℝ))
    (hYRadius :
      C.yRadius =
        fun y =>
          cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
            C2 kappa1 delta kappa (domainMetric y : ℝ))
    (hrow : ∀ target : PhysicalBond 4 (M * (2 * Q)),
      ∑ source : PhysicalBond 4 (M * (2 * Q)),
        Real.exp (-(cmp116Eq219InternalRate M kappa1 *
          (physicalBondDist target source : ℝ))) ≤ rowSum)
    (hgeometry : ∀ y source target,
      kernelSupport y source target →
        cmp116Eq219InternalRate M kappa1 *
            (physicalBondDist target source : ℝ) ≤
          (1 / 4 : ℝ) * (kappa1 - 1) *
            ((M : ℝ) ^ 4)⁻¹ * domainCard y)
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
      |residual sigma
        (restrictGlobal C.spectatorSupport psi)
        (restrictGlobal C.fluctuationSupport phi) y
        (physicalBondProjection
          (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
          (cmp116SourcePhysicalCoordinateCochain b))| ≤
        cmp116Eq136ResidualMajorant E0 epsilon1 C1 M q
          C2 kappa1 delta kappa (domainMetric y : ℝ))
    {gamma alpha : ℝ}
    (hgamma : 0 ≤ gamma)
    (hbudget :
      cmp116Eq220CenteredSourcePotentialRate Finset.univ
          (fun y => (domainMetric y : ℝ)) domainCard
          C3 epsilon1 M C2 kappa1 alpha4 rowSum +
        cmp116SourcePi4PhysicalComplexR2BilateralBound
          K Delta Ahead rho rate radius (1 + radius) +
        gamma ≤ alpha) :
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
        hradius (by simpa [Cphysical] using hradiusCap) hseries hneumann
    let SInner := cmp116SourcePhysicalLocalizedCoordinates Dict Z0
    let SOuter := cmp116SourcePhysicalLocalizedCoordinates Dict Z
    let Csource := Craw.withConditionedOuterCarrier SOuter
    ∀ sigma tau,
      CMP116Eq214ShiftedPolydisc nDelta Csource.deltaRadius sigma →
      CMP116Eq214CenteredPolydisc nY Csource.yRadius tau →
      ∀ᵐ b ∂matrixGaussianPi Csource.referenceRoot,
        (Csource.toLocalFiniteGaussianData.toFiniteGaussianData.interactionExponent
            sigma tau psi phi b).re +
          gamma / 2 *
            (∑ bond ∈ P,
              ‖Csource.toLocalFiniteGaussianData.toFiniteGaussianData.bondField
                b bond‖ ^ 2) ≤
          -((b ⬝ᵥ Matrix.mulVec
            (-(alpha • cmp116Eq223CoordinateProjection SInner)) b) / 2) +
            cmp116Eq220CenteredSourceResidual Finset.univ
              (fun y => (domainMetric y : ℝ))
              E0 epsilon1 C1 M q C2 kappa1 delta kappa alpha4 := by
  dsimp only
  let quadratic := fun sigma psi phi =>
    cmp116Eq142PhysicalSourceQuadratic
      (total sigma psi phi) (residual sigma psi phi)
      (hsmooth sigma psi phi)
  let CrawBase :=
    C.withSourcePi4RestrictedComplexGaussianOfPhysicalContour
      anchor contourCarrier hcarrier e Z0 K root
      hsourceRange hfiniteRange hc hmass hK hD
      hAhead hrho hrate hgeom Cert htri hDelta hDelta1
      hradius hradiusCap hseries hneumann
  let Cpost :=
    (CrawBase.withSourcePhysicalComplexTauPotential
      Dict Finset.univ quadratic residual Z0).withSourcePhysicalBondField
        threshold
  let SInner := cmp116SourcePhysicalLocalizedCoordinates Dict Z0
  let SOuter := cmp116SourcePhysicalLocalizedCoordinates Dict Z
  let Csource := Cpost.withConditionedOuterCarrier SOuter
  intro sigma tau hsigma htau
  have hsigmaC :
      CMP116Eq214ShiftedPolydisc nDelta C.deltaRadius sigma := by
    simpa [Csource, Cpost, CrawBase, quadratic] using hsigma
  have htauC :
      CMP116Eq214CenteredPolydisc nY
        (fun y =>
          cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
            C2 kappa1 delta kappa (domainMetric y : ℝ)) tau := by
    have htauBase :
        CMP116Eq214CenteredPolydisc nY C.yRadius tau := by
      simpa [Csource, Cpost, CrawBase, quadratic] using htau
    rw [hYRadius] at htauBase
    exact htauBase
  have hdiff : ∀ d,
      ‖cmp116SourceRestrictedShiftedCoupling
        contourCarrier e sigma d - 1‖ ≤ radius :=
    norm_cmp116SourceRestrictedShiftedCoupling_sub_one_le_radius
      contourCarrier e C.deltaRadius radius hradius hradiusCap sigma hsigmaC
  have hcap : ∀ d,
      ‖cmp116SourceRestrictedShiftedCoupling contourCarrier e sigma d‖ ≤
        1 + radius :=
    norm_cmp116SourceRestrictedShiftedCoupling_le_one_add_radius
      contourCarrier e C.deltaRadius radius hradius hradiusCap sigma hsigmaC
  have hR2raw :=
    bilateral_cmp116SourcePi4FullComplexR2Matrix_le_physical
      anchor K hsourceRange hfiniteRange hc hmass hK hD
      hAhead hrho hrate hgeom Cert htri hDelta hDelta1
      (cmp116SourceRestrictedShiftedCoupling contourCarrier e sigma)
      hradius (by linarith) hdiff hcap hseries hneumann hneumannTranspose
  have hR2 :
      (‖CrawBase.r2Matrix sigma tau
          (restrictGlobal CrawBase.spectatorSupport psi)
          (restrictGlobal CrawBase.fluctuationSupport phi)‖ +
        ‖(CrawBase.r2Matrix sigma tau
          (restrictGlobal CrawBase.spectatorSupport psi)
          (restrictGlobal CrawBase.fluctuationSupport phi)).transpose‖) / 2 ≤
          cmp116SourcePi4PhysicalComplexR2BilateralBound
            K Delta Ahead rho rate radius (1 + radius) := by
    simpa [CrawBase] using hR2raw
  have hinner :=
    CrawBase.ae_interactionExponent_le_sourcePhysicalAlpha5_of_centeredSource
      Dict Finset.univ total residual hsmooth kernelSupport
      (fun y => (domainMetric y : ℝ)) domainCard
      E0 epsilon1 C1 alpha4 C3 C2 kappa1 delta kappa rowSum threshold
      Z0 P sigma tau
      (restrictGlobal CrawBase.spectatorSupport psi)
      (restrictGlobal CrawBase.fluctuationSupport phi)
      conditionedCovariance
      (by simpa [CrawBase] using hroot)
      hE0 hepsilon1 hC1 halpha4 hC3 hC3upper hM hq hkappa1 hkappa
      (fun y _ => hdomainDist y) htauC hrow
      (fun y _ => hgeometry y)
      (fun b y _ => hzeroB sigma hsigmaC b y)
      (fun b y _ => h143 sigma hsigmaC b y)
      (fun b y _ => h136 sigma hsigmaC b y)
      hR2 hgamma hbudget
  have houter :=
    Cpost.ae_interactionExponent_le_withConditionedOuterCarrier
      SOuter SInner P sigma tau
      (restrictGlobal Cpost.spectatorSupport psi)
      (restrictGlobal Cpost.fluctuationSupport phi)
      gamma alpha
      (cmp116Eq220CenteredSourceResidual Finset.univ
        (fun y => (domainMetric y : ℝ))
        E0 epsilon1 C1 M q C2 kappa1 delta kappa alpha4)
      (by simpa [Cpost, CrawBase, quadratic, SInner] using hinner)
  filter_upwards [houter] with b hb
  have hprojection :
      -((b ⬝ᵥ Matrix.mulVec
          (-(alpha • cmp116Eq223CoordinateProjection SInner)) b) / 2) =
        alpha / 2 * (∑ i ∈ SInner, b i ^ 2) := by
    rw [Matrix.neg_mulVec, Matrix.smul_mulVec,
      dotProduct_neg, dotProduct_smul,
      dotProduct_projection_mulVec]
    simp only [smul_eq_mul]
    ring
  simpa [Csource, Cpost, CrawBase, quadratic, SInner, SOuter, hprojection]
    using hb

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
