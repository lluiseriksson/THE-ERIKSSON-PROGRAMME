/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourceRestrictedConditionedPhysicalEq226PhysicalBoundary
import YangMills.RG.BalabanCMP116RadialTaylorBound

/-!
# A source-faithful conditioned physical equation-(2.26) term

The older `CMP116Eq226PhysicalContourTermSource` stores a pointwise estimate
of the interaction exponent.  That interface is not suitable for the
physical density: the bilinear fluctuation factor is controlled only after
integration, and the correct interaction estimate is almost everywhere for
the conditioned Gaussian measure.

This file packages only the data that precede the conditioned density and the
genuine source obligations used to construct its bound.  In particular, the
record contains no statement mentioning the final analytic term, the
analytic integrand, an interaction exponent, a Gaussian measure, or a Cauchy
boundary majorant.  Its termwise estimate is derived by the physical theorem
`norm_term_le_eq226SourceTermWeight_of_sourcePi4ConditionedPhysicalPotentialLedger`.
-/

namespace YangMills.RG

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator

private abbrev SourceBond (M Q : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)] [NeZero (M * (2 * Q))] :=
  PhysicalBond 4 (M * (2 * Q))

private abbrev SourceEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)] [NeZero (M * (2 * Q))] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- Physical input data for one conditioned equation-(2.14) summand.

Every proof field is either a structural certificate, a printed source
estimate ((1.43)/(1.36)), or an explicit scalar/rooted ledger.  There is no
field equivalent to the final termwise estimate.  The equation-(1.36)
estimate is consumed only on the literal cutoff support; outside that support
the analytic integrand vanishes identically.  The mandatory covariance-lower
certificate prevents this almost-everywhere contract from being discharged
by a degenerate conditioned Gaussian. -/
structure CMP116Eq226ConditionedPhysicalTermSource
    {nDelta nY M Q Nc L lieDim : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))] [NeZero L] [NeZero lieDim]
    (Dict : PhysicalGaugeCMP116Dictionary
      4 (M * (2 * Q)) Nc 4 L lieDim)
    (Y0 P : Finset (SourceBond M Q))
    (Z0 Z : Finset (FinBox 4 (2 * Q))) where
  base :
    CMP116Eq214PhysicalContourDensity nDelta nY
      (SourceBond M Q) (SourceBond M Q)
      (fun _ => SUNLieCoord Nc) (fun _ => SUNLieCoord Nc)
      (SUNLieCoord Nc) (Nc ^ 2 - 1)
  anchor : FinBox 4 Q
  contourCarrier : Finset (FinBox 4 (2 * Q))
  carrier_subset_sigmaZero :
    contourCarrier ⊆ cmp116SourceSigmaZero anchor
  carrier_subset_Z0 : contourCarrier ⊆ Z0
  Z0_subset_Z : Z0 ⊆ Z
  contourEquiv : Fin nDelta ≃ ↥contourCarrier
  K : SourceEndomorphism M Q Nc
  root : SourceEndomorphism M Q Nc
  sourceRange : ℕ
  sourceRange_bound : sourceRange + 1 ≤ 4 * M
  finiteRange :
    PhysicalCovarianceFiniteRange K physicalBondDist sourceRange
  coercivityConstant : ℝ
  mass : ℝ
  coercivity_pos : 0 < coercivityConstant
  mass_pos : 0 < mass
  K_coercive : IsCoerciveCLM K coercivityConstant
  patchedDefect_small :
    ‖cmp99PatchedPhysicalParametrixDefect
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q))
        K cmp99SourcePi4ChartEnlarged
        (cmp99SourcePi4ChartCore (M := M))
        coercivity_pos mass_pos K_coercive‖ < 1
  Ahead : ℝ
  rho : ℝ
  rate : ℝ
  radius : ℝ
  Ahead_nonneg : 0 ≤ Ahead
  rho_nonneg : 0 ≤ rho
  rate_pos : 0 < rate
  shell_small : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1
  patchCertificate :
    CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      coercivity_pos mass_pos K_coercive physicalBondDist Ahead rho rate
  distance_triangle : ∀ target source middle : SourceBond M Q,
    physicalBondDist target source ≤
      physicalBondDist target middle + physicalBondDist middle source
  Delta : ℕ
  degree_bound : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Delta
  one_le_Delta : 1 ≤ Delta
  radius_nonneg : 0 ≤ radius
  radius_cap : ∀ i, 1 + base.deltaRadius i ≤ radius
  contour_series_small :
    ‖cmp116SourcePi4ComplexContourRatio Delta rho (1 + radius)‖ < 1
  neumann_small :
    ‖cmp116PhysicalEndomorphismComplexMatrix K‖ *
      cmp116SourcePi4PhysicalComplexContourDefectBound
        Nc Delta Ahead rho rate radius (1 + radius) < 1
  neumann_transpose_small :
    cmp116SourcePi4PhysicalComplexTransposeRelativeDefectBound
      K Delta Ahead rho rate radius (1 + radius) < 1
  quadratic :
    (Fin nDelta → ℂ) →
    RestrictedField base.spectatorSupport (fun _ => SUNLieCoord Nc) →
    RestrictedField base.fluctuationSupport (fun _ => SUNLieCoord Nc) →
    Fin nY → PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →
      SourceEndomorphism M Q Nc
  total :
    (Fin nDelta → ℂ) →
    RestrictedField base.spectatorSupport (fun _ => SUNLieCoord Nc) →
    RestrictedField base.fluctuationSupport (fun _ => SUNLieCoord Nc) →
    Fin nY → PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc → ℝ
  remainder :
    (Fin nDelta → ℂ) →
    RestrictedField base.spectatorSupport (fun _ => SUNLieCoord Nc) →
    RestrictedField base.fluctuationSupport (fun _ => SUNLieCoord Nc) →
    Fin nY → PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc → ℝ
  amplitude : Fin nY → ℝ
  alpha : ℝ
  gamma : ℝ
  qBound : ℝ
  qBound_nonneg : 0 ≤ qBound
  qBound_lt_one : qBound < 1
  E0 : ℝ
  epsilon1 : ℝ
  C1 : ℝ
  alpha4 : ℝ
  C2 : ℝ
  kappa1 : ℝ
  delta : ℝ
  kappa : ℝ
  gk : ℝ
  q : ℕ
  domainMetric : Fin nY → ℕ
  domainSupport : Fin nY → Finset (FinBox 4 (2 * Q))
  gapScale : ℕ
  gapCard : ℕ
  rootBound : ℝ
  volumeRate : ℝ
  rowSum : ℝ
  threshold : ℝ
  potentialRate : ℝ
  conditionedCovariance :
    Matrix
      (PhysicalGaugeCoordIndex 4 (M * (2 * Q)) Nc)
      (PhysicalGaugeCoordIndex 4 (M * (2 * Q)) Nc) ℝ
  conditionedRoot :
    MatrixConditionedGaussianRootCertificate
      conditionedCovariance
      (cmp116PhysicalEndomorphismRealMatrix root)
      (cmp116SourcePhysicalLocalizedCoordinates Dict Z0)
  conditionedCovariance_nondegenerate :
    MatrixConditionedGaussianCovarianceLowerCertificate
      conditionedCovariance
      (cmp116SourcePhysicalLocalizedCoordinates Dict Z0)
  rowSum_nonneg : 0 ≤ rowSum
  exponential_row_bound : ∀ target : SourceBond M Q,
    ∑ source : SourceBond M Q,
      Real.exp (-(kappa *
        (physicalBondDist target source : ℝ))) ≤ rowSum
  amplitude_nonneg : ∀ y, 0 ≤ amplitude y
  kappa_pos : 0 < kappa
  quadratic_smooth : ∀ sigma psi phi,
    ∀ y,
      ContDiff ℝ 2
        (cmp116Eq142PhysicalQuadraticCore
          (fun y B =>
            total sigma
              (restrictGlobal base.spectatorSupport psi)
              (restrictGlobal base.fluctuationSupport phi) y B)
          (fun y B =>
            remainder sigma
              (restrictGlobal base.spectatorSupport psi)
              (restrictGlobal base.fluctuationSupport phi) y B)
          y)
  quadratic_eq_radial : ∀ sigma psi phi y B,
    quadratic sigma
        (restrictGlobal base.spectatorSupport psi)
        (restrictGlobal base.fluctuationSupport phi) y B =
      cmp116Eq142PhysicalSourceQuadratic
        (fun y B =>
          total sigma
            (restrictGlobal base.spectatorSupport psi)
            (restrictGlobal base.fluctuationSupport phi) y B)
        (fun y B =>
          remainder sigma
            (restrictGlobal base.spectatorSupport psi)
            (restrictGlobal base.fluctuationSupport phi) y B)
        (quadratic_smooth sigma psi phi) y B
  radial_hessian_bound : ∀ psi phi sigma,
    CMP116Eq214ShiftedPolydisc nDelta base.deltaRadius sigma →
    ∀ b y,
      ∀ source target (v w : SUNLieCoord Nc),
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          |cmp116FDerivHessian
            (cmp116Eq142PhysicalQuadraticCore
              (fun y B =>
                total sigma
                  (restrictGlobal base.spectatorSupport psi)
                  (restrictGlobal base.fluctuationSupport phi) y B)
              (fun y B =>
                remainder sigma
                  (restrictGlobal base.spectatorSupport psi)
                  (restrictGlobal base.fluctuationSupport phi) y B)
              y)
            (t •
              physicalBondProjection
                (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
                (cmp116SourcePhysicalCoordinateCochain b))
            (singlePhysicalBondCochain
              (d := 4) (N := M * (2 * Q)) (Nc := Nc) source v)
            (singlePhysicalBondCochain
              (d := 4) (N := M * (2 * Q)) (Nc := Nc) target w)| ≤
            amplitude y *
              Real.exp (-(kappa *
                (physicalBondDist target source : ℝ))) * ‖v‖ * ‖w‖
  remainder_bound : ∀ psi phi sigma tau,
    CMP116Eq214ShiftedPolydisc nDelta base.deltaRadius sigma →
    CMP116Eq214ShiftedPolydisc nY base.yRadius tau →
    ∀ b y,
      ‖tau y‖ *
          |remainder sigma
            (restrictGlobal base.spectatorSupport psi)
            (restrictGlobal base.fluctuationSupport phi) y
            (physicalBondProjection
              (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
              (cmp116SourcePhysicalCoordinateCochain b))| ≤
        cmp116Eq220ResidualDomainWeight alpha4 delta kappa
          (domainMetric y : ℝ)
  potential_rate_bound : ∀ tau,
    CMP116Eq214ShiftedPolydisc nY base.yRadius tau →
    (∑ y : Fin nY, ‖tau y‖ * amplitude y * rowSum) ≤ potentialRate
  interaction_budget :
    potentialRate +
        cmp116SourcePi4PhysicalComplexR2BilateralBound
          K Delta Ahead rho rate radius (1 + radius) +
        gamma ≤ alpha
  deltaRadius_eq :
    let Cphysical :=
      (base.withSourcePhysicalComplexTauPotential
        Dict Finset.univ quadratic remainder Z0).withSourcePhysicalBondField
          threshold
    (Cphysical.withSourcePi4RestrictedComplexGaussianOfPhysicalContour
      anchor contourCarrier carrier_subset_sigmaZero contourEquiv Z0 K root
      sourceRange_bound finiteRange coercivity_pos mass_pos K_coercive
      patchedDefect_small Ahead_nonneg rho_nonneg rate_pos shell_small
      patchCertificate distance_triangle degree_bound one_le_Delta
      radius_nonneg (by simpa [Cphysical] using radius_cap)
      contour_series_small neumann_small).deltaRadius =
        fun _ => cmp116Eq214SigmaCauchyRadius kappa1
  normalizedGap :
    ((((gapScale * M : ℕ) : ℝ) ^ 4)⁻¹ * (gapCard : ℝ)) =
      (nDelta : ℝ)
  yRadius_eq :
    let Cphysical :=
      (base.withSourcePhysicalComplexTauPotential
        Dict Finset.univ quadratic remainder Z0).withSourcePhysicalBondField
          threshold
    (Cphysical.withSourcePi4RestrictedComplexGaussianOfPhysicalContour
      anchor contourCarrier carrier_subset_sigmaZero contourEquiv Z0 K root
      sourceRange_bound finiteRange coercivity_pos mass_pos K_coercive
      patchedDefect_small Ahead_nonneg rho_nonneg rate_pos shell_small
      patchCertificate distance_triangle degree_bound one_le_Delta
      radius_nonneg (by simpa [Cphysical] using radius_cap)
      contour_series_small neumann_small).yRadius =
        fun Y =>
          cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
            C2 kappa1 delta kappa (domainMetric Y : ℝ)
  E0_pos : 0 < E0
  epsilon1_pos : 0 < epsilon1
  C1_pos : 0 < C1
  alpha4_pos : 0 < alpha4
  one_le_M : 1 ≤ M
  gk_ne : gk ≠ 0
  threshold_eq :
    let Cphysical :=
      (base.withSourcePhysicalComplexTauPotential
        Dict Finset.univ quadratic remainder Z0).withSourcePhysicalBondField
          threshold
    (Cphysical.withSourcePi4RestrictedComplexGaussianOfPhysicalContour
      anchor contourCarrier carrier_subset_sigmaZero contourEquiv Z0 K root
      sourceRange_bound finiteRange coercivity_pos mass_pos K_coercive
      patchedDefect_small Ahead_nonneg rho_nonneg rate_pos shell_small
      patchCertificate distance_triangle degree_bound one_le_Delta
      radius_nonneg (by simpa [Cphysical] using radius_cap)
      contour_series_small neumann_small).threshold = epsilon1 / gk
  alpha_nonneg : 0 ≤ alpha
  root_small :
    alpha *
      (@norm
        (Matrix
          (PhysicalGaugeCoordIndex 4 (M * (2 * Q)) Nc)
          (PhysicalGaugeCoordIndex 4 (M * (2 * Q)) Nc) ℝ)
        Matrix.instL2OpNormedAddCommGroup.toNorm
        (cmp116PhysicalEndomorphismRealMatrix root)) ^ 2 < 1
  gamma_nonneg : 0 ≤ gamma
  threshold_nonneg : 0 ≤ threshold
  outer_small :
    2 *
      (cmp116SourcePi4PhysicalComplexR1DefectBilateralBudget
          K root coercivity_pos mass_pos K_coercive Z0 Delta
            Ahead rho rate radius (1 + radius) +
        |cmp116Eq225SourceCoefficient
            (cmp116PhysicalEndomorphismRealMatrix root) alpha *
          cmp116SourcePi4PhysicalComplexR3SourceRate
            K root Z0 Delta Ahead rho rate radius (1 + radius)|) ≤
      qBound
  domain_nonempty : ∀ Y : Fin nY, (domainSupport Y).Nonempty
  domain_subset : ∀ Y : Fin nY, domainSupport Y ⊆ Z0
  rootBound_nonneg : 0 ≤ rootBound
  rooted_residual : ∀ i ∈ Z0,
    ∑ Y ∈ (Finset.univ.filter fun Y : Fin nY =>
        i ∈ domainSupport Y),
      cmp116Eq220ResidualDomainWeight alpha4 delta kappa
        (domainMetric Y : ℝ) ≤ rootBound
  volume_budget :
    rootBound +
        cmp116SourceRestrictedConditionedPhysicalOuterPerCarrierCost
          K root coercivity_pos mass_pos K_coercive Z0 Delta radius rate
            Ahead rho alpha
            (cmp116SourcePi4PhysicalComplexR3SourceRate
              K root Z0 Delta Ahead rho rate radius (1 + radius))
            qBound
            (cmp116SourceRestrictedUniformContourDeterminantCost
              M Nc Delta radius (1 + radius) rate Ahead rho
                ‖cmp116PhysicalEndomorphismComplexMatrix K‖) ≤
      volumeRate * alpha

namespace CMP116Eq226ConditionedPhysicalTermSource

variable
    {nDelta nY M Q Nc L lieDim : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))] [NeZero L] [NeZero lieDim]
    {Dict : PhysicalGaugeCMP116Dictionary
      4 (M * (2 * Q)) Nc 4 L lieDim}
    {Y0 P : Finset (SourceBond M Q)}
    {Z0 Z : Finset (FinBox 4 (2 * Q))}

/-- The fully assembled conditioned density generated from the stored source
data. -/
noncomputable def conditionedDensity
    (S : CMP116Eq226ConditionedPhysicalTermSource
      (nDelta := nDelta) (nY := nY) Dict Y0 P Z0 Z) :=
  let Cphysical :=
    (S.base.withSourcePhysicalComplexTauPotential
      Dict Finset.univ S.quadratic S.remainder Z0).withSourcePhysicalBondField
        S.threshold
  let Craw :=
    Cphysical.withSourcePi4RestrictedComplexGaussianOfPhysicalContour
      S.anchor S.contourCarrier S.carrier_subset_sigmaZero S.contourEquiv
      Z0 S.K S.root S.sourceRange_bound S.finiteRange
      S.coercivity_pos S.mass_pos S.K_coercive S.patchedDefect_small
      S.Ahead_nonneg S.rho_nonneg S.rate_pos S.shell_small
      S.patchCertificate S.distance_triangle S.degree_bound S.one_le_Delta
      S.radius_nonneg (by simpa [Cphysical] using S.radius_cap)
      S.contour_series_small S.neumann_small
  Craw.withConditionedOuterCarrier
    (cmp116SourcePhysicalLocalizedCoordinates Dict Z)

/-- The literal equation-(2.26) weight on the outer conditioned carrier. -/
noncomputable def termWeight
    (S : CMP116Eq226ConditionedPhysicalTermSource
      (nDelta := nDelta) (nY := nY) Dict Y0 P Z0 Z) : ℝ :=
  cmp116Eq226SourceTermWeight S.E0 S.epsilon1 S.C1 S.alpha4 M S.q
    S.C2 S.kappa1 S.delta S.kappa S.gamma S.gk S.gapScale S.gapCard
    S.volumeRate S.alpha Z.card S.domainMetric Finset.univ P

set_option maxHeartbeats 20000000 in
/-- The physical source record derives its termwise equation-(2.26) estimate.
The almost-everywhere interaction estimate is produced and consumed inside
the invoked theorem; it is not stored in the record. -/
theorem norm_term_le_termWeight
    (S : CMP116Eq226ConditionedPhysicalTermSource
      (nDelta := nDelta) (nY := nY) Dict Y0 P Z0 Z)
    (psi phi : PhysicalGaugeField 4 (M * (2 * Q)) Nc) :
    ‖S.conditionedDensity.toLocalFiniteGaussianData.toFiniteGaussianData
        |>.toAnalyticData.term Y0 P psi phi‖ ≤
      S.termWeight := by
  have hquadratic : ∀ sigma,
      CMP116Eq214ShiftedPolydisc nDelta S.base.deltaRadius sigma →
      ∀ b y,
        PhysicalCovarianceExponentialKernelBound
          (S.quadratic sigma
            (restrictGlobal S.base.spectatorSupport psi)
            (restrictGlobal S.base.fluctuationSupport phi) y
            (physicalBondProjection
              (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
              (cmp116SourcePhysicalCoordinateCochain b)))
          physicalBondDist (S.amplitude y) S.kappa := by
    intro sigma hsigma b y
    rw [S.quadratic_eq_radial sigma psi phi y]
    exact
      physicalCovarianceExponentialKernelBound_cmp116Eq142PhysicalSourceQuadratic_of_hessian
        (fun y B =>
          S.total sigma
            (restrictGlobal S.base.spectatorSupport psi)
            (restrictGlobal S.base.fluctuationSupport phi) y B)
        (fun y B =>
          S.remainder sigma
            (restrictGlobal S.base.spectatorSupport psi)
            (restrictGlobal S.base.fluctuationSupport phi) y B)
        (S.quadratic_smooth sigma psi phi) y
        (physicalBondProjection
          (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
          (cmp116SourcePhysicalCoordinateCochain b))
        physicalBondDist (S.amplitude y) S.kappa
        (S.amplitude_nonneg y) S.kappa_pos
        (S.radial_hessian_bound psi phi sigma hsigma b y)
  unfold conditionedDensity termWeight
  exact
    S.base.norm_term_le_eq226SourceTermWeight_of_sourcePi4ConditionedPhysicalPotentialLedger
      Dict S.anchor S.contourCarrier Z0 Z
      S.carrier_subset_sigmaZero S.carrier_subset_Z0 S.Z0_subset_Z
      S.contourEquiv S.K S.root S.sourceRange_bound S.finiteRange
      S.coercivity_pos S.mass_pos S.K_coercive S.patchedDefect_small
      S.Ahead_nonneg S.rho_nonneg S.rate_pos S.shell_small
      S.patchCertificate S.distance_triangle S.degree_bound S.one_le_Delta
      S.radius_nonneg S.radius_cap S.contour_series_small S.neumann_small
      S.neumann_transpose_small S.quadratic S.remainder S.amplitude
      Y0 P psi phi S.alpha S.gamma S.qBound_nonneg S.qBound_lt_one
      S.domainMetric S.domainSupport S.gapScale S.gapCard S.rootBound
      S.volumeRate S.rowSum S.threshold S.potentialRate
      S.conditionedCovariance S.conditionedRoot
      S.conditionedCovariance_nondegenerate S.rowSum_nonneg
      S.exponential_row_bound hquadratic
      (S.remainder_bound psi phi) S.potential_rate_bound
      S.interaction_budget S.deltaRadius_eq S.normalizedGap S.yRadius_eq
      S.E0_pos S.epsilon1_pos S.C1_pos S.alpha4_pos S.one_le_M S.gk_ne
      S.threshold_eq S.alpha_nonneg S.root_small S.gamma_nonneg
      S.threshold_nonneg S.outer_small S.domain_nonempty S.domain_subset
      S.rootBound_nonneg S.rooted_residual S.volume_budget

end CMP116Eq226ConditionedPhysicalTermSource

end

end YangMills.RG
