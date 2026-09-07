/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourceRestrictedPhysicalAEInteractionBoundary
import YangMills.RG.BalabanCMP116Eq223PhysicalLocalizationProjector
import YangMills.RG.BalabanCMP116Eq220ConditionedResidualLedger

/-!
# Physical producer of the conditioned equation-(2.26) interaction boundary

The conclusion of this module is the almost-everywhere interaction premise
used by the conditioned equation-(2.26) theorem.  It is generated uniformly
on the two shifted Cauchy polydiscs from the literal source potential, the
physical `R2` Neumann bounds, the literal bond field, and a certified
conditioned covariance root.
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

set_option maxHeartbeats 4000000 in
/-- Source-specific producer of the exact AE interaction boundary consumed
by the conditioned equation-(2.26) theorem. -/
theorem
    ae_interactionBoundary_of_sourcePi4ConditionedPhysicalPotential
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
    (domainMetric : Fin nY → ℕ)
    {alpha4 delta kappa rowSum threshold potentialRate gamma alpha : ℝ}
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
    (hgamma : 0 ≤ gamma)
    (hbudget :
      potentialRate +
          cmp116SourcePi4PhysicalComplexR2BilateralBound
            K Delta Ahead rho rate radius (1 + radius) +
          gamma ≤ alpha) :
    let Cphysical :=
      (C.withSourcePhysicalComplexTauPotential
        Dict Finset.univ quadratic remainder Z0).withSourcePhysicalBondField
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
      CMP116Eq214ShiftedPolydisc nY Csource.yRadius tau →
      ∀ᵐ b ∂matrixGaussianPi Csource.referenceRoot,
        (Csource.toLocalFiniteGaussianData.toFiniteGaussianData.interactionExponent
            sigma tau psi phi b).re +
          gamma / 2 *
            (∑ bond ∈ P,
              ‖Csource.toLocalFiniteGaussianData.toFiniteGaussianData.bondField
                b bond‖ ^ 2) ≤
          -((b ⬝ᵥ Matrix.mulVec
            (-(alpha • cmp116Eq223CoordinateProjection SInner)) b) / 2) +
            ∑ Y : Fin nY,
              cmp116Eq220ResidualDomainWeight alpha4 delta kappa
                (domainMetric Y : ℝ) := by
  dsimp only
  let Cphysical :=
    (C.withSourcePhysicalComplexTauPotential
      Dict Finset.univ quadratic remainder Z0).withSourcePhysicalBondField
        threshold
  let Craw :=
    Cphysical.withSourcePi4RestrictedComplexGaussianOfPhysicalContour
      anchor contourCarrier hcarrier e Z0 K root
      hsourceRange hfiniteRange hc hmass hK hD
      hAhead hrho hrate hgeom Cert htri hDelta hDelta1
      hradius (by simpa [Cphysical] using hradiusCap) hseries hneumann
  let CrawBase :=
    C.withSourcePi4RestrictedComplexGaussianOfPhysicalContour
      anchor contourCarrier hcarrier e Z0 K root
      hsourceRange hfiniteRange hc hmass hK hD
      hAhead hrho hrate hgeom Cert htri hDelta hDelta1
      hradius hradiusCap hseries hneumann
  let Cpost :=
    (CrawBase.withSourcePhysicalComplexTauPotential
      Dict Finset.univ quadratic remainder Z0).withSourcePhysicalBondField
        threshold
  let SInner := cmp116SourcePhysicalLocalizedCoordinates Dict Z0
  let SOuter := cmp116SourcePhysicalLocalizedCoordinates Dict Z
  let Csource := Craw.withConditionedOuterCarrier SOuter
  intro sigma tau hsigma htau
  have hsigmaC :
      CMP116Eq214ShiftedPolydisc nDelta C.deltaRadius sigma := by
    simpa [Csource, Craw, Cphysical] using hsigma
  have htauC :
      CMP116Eq214ShiftedPolydisc nY C.yRadius tau := by
    simpa [Csource, Craw, Cphysical] using htau
  have hinner :=
    C.ae_interactionExponent_le_sourcePi4RestrictedPhysicalAlpha5
      (kappa := kappa) (rowSum := rowSum) (threshold := threshold)
      (potentialRate := potentialRate) (gamma := gamma) (alpha := alpha)
      Dict anchor contourCarrier hcarrier e Z0 K root
      hsourceRange hfiniteRange hc hmass hK hD
      hAhead hrho hrate hgeom Cert htri hDelta hDelta1
      hradius hradiusCap hseries hneumann hneumannTranspose
      Finset.univ quadratic remainder amplitude
      (fun Y => cmp116Eq220ResidualDomainWeight
        alpha4 delta kappa (domainMetric Y : ℝ))
      P sigma tau psi phi hsigmaC conditionedCovariance hroot
      hrowSum hrow
      (fun b y _ => hquadratic sigma hsigmaC b y)
      (fun b y _ => hremainder sigma tau hsigmaC htauC b y)
      (by simpa using hpotentialRate tau htauC)
      hgamma hbudget
  have houter :=
    Cpost.ae_interactionExponent_le_withConditionedOuterCarrier
      SOuter SInner P sigma tau
      (restrictGlobal Cpost.spectatorSupport psi)
      (restrictGlobal Cpost.fluctuationSupport phi)
      gamma alpha
      (∑ Y : Fin nY,
        cmp116Eq220ResidualDomainWeight alpha4 delta kappa
          (domainMetric Y : ℝ))
      (by simpa [Cpost, CrawBase, SInner] using hinner)
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
  simpa [Csource, Craw, Cphysical, Cpost, CrawBase, SInner,
    SOuter, hprojection] using hb

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
