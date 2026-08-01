/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq220CenteredPhysicalQuadraticRate
import YangMills.RG.BalabanCMP116SourceCenteredPhysicalAEInteraction

/-!
# Centered physical interaction with a genuine quadratic residual budget

This module refines the centered source interaction theorem at the precise
equation-(1.36) frontier.  The equation-(1.43) quadratic rate is produced
internally from the literal physical Hessian.  The interpolation-center value
of the genuine Taylor residual is charged to a separate localized quadratic
rate, while only its centered-contour displacement is entered in the printed
equation-(2.20) residual ledger.

The physical cubic estimate producing `residualRate` and the scalar stability
budget remain explicit hypotheses.  In particular, this theorem does not call
equation (1.36) proved and does not duplicate its majorant in the final ledger.
-/

namespace YangMills.RG

open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.Operator

noncomputable section

namespace CMP116Eq214PhysicalContourDensity

set_option maxHeartbeats 4000000 in
/-- The literal equation-(1.43) Hessian bound and a genuine centered Taylor
residual rate imply the AE interaction estimate with exactly one Eq220 weight
per localization domain.

The sum of the residual rates is exposed as `residualPotentialRate`; it is not
silently absorbed into the printed residual ledger. -/
theorem ae_interactionExponent_le_sourcePhysicalAlpha5_of_centeredQuadraticResidual
    {nDelta nY d M N' Nc L lieDim q : ℕ}
    {Site : Type*} {Psi Phi : Site → Type*}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero (Nc ^ 2 - 1)] [NeZero L] [NeZero lieDim]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d (M * N')) Site Psi Phi
        (SUNLieCoord Nc) (Nc ^ 2 - 1))
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (D : Finset (Fin nY))
    (total residual :
      (Fin nDelta → ℂ) →
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      Fin nY → PhysicalGaugeOneCochain d (M * N') Nc → ℝ)
    (hsmooth : ∀ sigma psi phi y,
      ContDiff ℝ 2
        (cmp116Eq142PhysicalQuadraticCore
          (total sigma psi phi) (residual sigma psi phi) y))
    (kernelSupport :
      Fin nY → PhysicalBond d (M * N') →
        PhysicalBond d (M * N') → Prop)
    (domainDist : Fin nY → ℝ) (domainCard : Fin nY → ℕ)
    (E0 epsilon1 C1 alpha4 C3 C2 kappa1 delta kappa rowSum threshold :
      ℝ)
    (Z0 : Finset (FinBox d N'))
    (P : Finset (PhysicalBond d (M * N')))
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (conditionedCovariance :
      Matrix (PhysicalGaugeCoordIndex d (M * N') Nc)
        (PhysicalGaugeCoordIndex d (M * N') Nc) ℝ)
    (hroot :
      MatrixConditionedGaussianRootCertificate
        conditionedCovariance C.referenceRoot
        (cmp116SourcePhysicalLocalizedCoordinates Dict Z0))
    (hE0 : 0 < E0) (hepsilon1 : 0 < epsilon1)
    (hC1 : 0 < C1) (halpha4 : 0 < alpha4)
    (hC3 : 0 ≤ C3) (hC3upper : C3 ≤ E0 * C1)
    (hM : 1 ≤ M) (hq : 8 ≤ q) (hkappa1 : 1 < kappa1)
    (hkappa :
      (1 - 3 * delta) * kappa ≤ (1 / 8 : ℝ) * (kappa1 - 1))
    (hdomainDist : ∀ y ∈ D, 0 ≤ domainDist y)
    (hcentered :
      CMP116Eq214CenteredPolydisc nY
        (fun y =>
          cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
            C2 kappa1 delta kappa (domainDist y))
        tau)
    (hrow : ∀ target : PhysicalBond d (M * N'),
      ∑ source : PhysicalBond d (M * N'),
        Real.exp (-(cmp116Eq219InternalRate M kappa1 *
          (physicalBondDist target source : ℝ))) ≤ rowSum)
    (hgeometry : ∀ y ∈ D, ∀ source target,
      kernelSupport y source target →
        cmp116Eq219InternalRate M kappa1 *
            (physicalBondDist target source : ℝ) ≤
          (1 / 4 : ℝ) * (kappa1 - 1) * domainCard y)
    (hzeroB : ∀ b y, y ∈ D → ∀ source target,
      ¬ kernelSupport y source target →
        ∀ (v w : SUNLieCoord Nc), ∀ t ∈ Set.Icc (0 : ℝ) 1,
          cmp116FDerivHessian
            (cmp116Eq142PhysicalQuadraticCore
              (total sigma psi phi) (residual sigma psi phi) y)
            (t • physicalBondProjection
              (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds
                Z0)
              (cmp116SourcePhysicalCoordinateCochain b))
            (singlePhysicalBondCochain
              (d := d) (N := M * N') (Nc := Nc) source v)
            (singlePhysicalBondCochain
              (d := d) (N := M * N') (Nc := Nc) target w) = 0)
    (h143 : ∀ b y, y ∈ D → ∀ source target (v w : SUNLieCoord Nc),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |cmp116FDerivHessian
          (cmp116Eq142PhysicalQuadraticCore
            (total sigma psi phi) (residual sigma psi phi) y)
          (t • physicalBondProjection
            (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds
              Z0)
            (cmp116SourcePhysicalCoordinateCochain b))
          (singlePhysicalBondCochain
            (d := d) (N := M * N') (Nc := Nc) source v)
          (singlePhysicalBondCochain
            (d := d) (N := M * N') (Nc := Nc) target w)| ≤
          cmp116Eq143QMajorant C3 epsilon1 M C2 kappa1
            (domainDist y) (domainCard y) * ‖v‖ * ‖w‖)
    (residualRate : Fin nY → ℝ)
    (residualPotentialRate : ℝ)
    (hresidualCenter : ∀ b y, y ∈ D →
      |residual sigma psi phi y
        (physicalBondProjection
          (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
          (cmp116SourcePhysicalCoordinateCochain b))| ≤
        residualRate y / 2 *
          (∑ ba ∈ cmp116SourcePhysicalLocalizedCoordinates Dict Z0,
            b ba ^ 2))
    (h136 : ∀ b y, y ∈ D →
      |residual sigma psi phi y
        (physicalBondProjection
          (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
          (cmp116SourcePhysicalCoordinateCochain b))| ≤
        cmp116Eq136ResidualMajorant E0 epsilon1 C1 M q
          C2 kappa1 delta kappa (domainDist y))
    (hresidualRate :
      ∑ y ∈ D, residualRate y ≤ residualPotentialRate)
    {r2Rate gamma alpha : ℝ}
    (hR2 :
      (‖C.r2Matrix sigma tau psi phi‖ +
        ‖(C.r2Matrix sigma tau psi phi).transpose‖) / 2 ≤ r2Rate)
    (hgamma : 0 ≤ gamma)
    (hbudget :
      cmp116Eq220CenteredSourcePotentialRate D domainDist domainCard
          C3 epsilon1 M C2 kappa1 alpha4 rowSum +
        residualPotentialRate + r2Rate + gamma ≤ alpha) :
    let quadratic := fun sigma psi phi =>
      cmp116Eq142PhysicalSourceQuadratic
        (total sigma psi phi) (residual sigma psi phi)
        (hsmooth sigma psi phi)
    let Csource :=
      (C.withSourcePhysicalComplexTauPotential
        Dict D quadratic residual Z0).withSourcePhysicalBondField threshold
    ∀ᵐ b ∂matrixGaussianPi Csource.referenceRoot,
      (Csource.toLocalFiniteGaussianData.interactionExponent
          sigma tau psi phi b).re +
        gamma / 2 *
          (∑ bond ∈ P, ‖Csource.bondField b bond‖ ^ 2) ≤
        alpha / 2 *
          (∑ ba ∈ cmp116SourcePhysicalLocalizedCoordinates Dict Z0,
            b ba ^ 2) +
          ∑ y ∈ D,
            cmp116Eq220ResidualDomainWeight alpha4 delta kappa
              (domainDist y) := by
  dsimp only
  let quadratic := fun sigma psi phi =>
    cmp116Eq142PhysicalSourceQuadratic
      (total sigma psi phi) (residual sigma psi phi)
      (hsmooth sigma psi phi)
  let Cpotential :=
    C.withSourcePhysicalComplexTauPotential
      Dict D quadratic residual Z0
  let S :=
    PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds
      (d := d) (M := M) (N' := N') Z0
  let quadraticRate := fun y =>
    (cmp116Eq143CenterDomainAmplitude C3 epsilon1 M C2 kappa1
        (domainDist y) (domainCard y) +
      cmp116Eq219DomainAmplitude alpha4 M kappa1 (domainCard y)) *
        rowSum
  let potentialRate :=
    cmp116Eq220CenteredSourcePotentialRate D domainDist domainCard
        C3 epsilon1 M C2 kappa1 alpha4 rowSum +
      residualPotentialRate
  let potentialResidual :=
    ∑ y ∈ D,
      cmp116Eq220ResidualDomainWeight alpha4 delta kappa (domainDist y)
  have hpotential :
      ∀ᵐ b ∂matrixGaussianPi Cpotential.referenceRoot,
        (Cpotential.potential sigma tau psi phi b).re ≤
          potentialRate / 2 *
              (∑ ba ∈ cmp116SourcePhysicalLocalizedCoordinates Dict Z0,
                b ba ^ 2) +
            potentialResidual := by
    filter_upwards [] with b
    let B := physicalBondProjection S
      (cmp116SourcePhysicalCoordinateCochain b)
    have hsupportB : ∀ i, i ∉ S → B i = 0 := by
      intro i hi
      exact physicalBondProjection_apply_not_mem S hi _
    have henergy :
        (∑ bond ∈ S, ‖B bond‖ ^ 2) =
          ∑ ba ∈ cmp116SourcePhysicalLocalizedCoordinates Dict Z0,
            b ba ^ 2 := by
      calc
        (∑ bond ∈ S, ‖B bond‖ ^ 2) =
            ∑ bond ∈ S,
              ‖cmp116SourcePhysicalCoordinateCochain b bond‖ ^ 2 := by
                apply Finset.sum_congr rfl
                intro bond hbond
                rw [physicalBondProjection_apply_mem S hbond]
        _ = ∑ ba ∈ cmp116SourcePhysicalLocalizedCoordinates Dict Z0,
            b ba ^ 2 := by
              simpa [S] using
                sum_norm_sq_cmp116SourcePhysicalCoordinateCochain Dict Z0 b
    have hquadratic : ∀ y ∈ D,
        ‖tau y‖ *
            |inner ℝ B
              (cmp116Eq142PhysicalSourceQuadratic
                (total sigma psi phi) (residual sigma psi phi)
                (hsmooth sigma psi phi) y B B)| ≤
          quadraticRate y *
            (∑ ba ∈ cmp116SourcePhysicalLocalizedCoordinates Dict Z0,
              b ba ^ 2) := by
      intro y hy
      have hq :=
        cmp116Eq220_centeredPhysicalQuadratic_le_rate
          S tau (total sigma psi phi) (residual sigma psi phi)
          (hsmooth sigma psi phi) B kernelSupport domainDist domainCard
          E0 epsilon1 C1 alpha4 C3 C2 kappa1 delta kappa M q rowSum y
          hE0 hepsilon1 hC1 halpha4 hC3 hC3upper hM hq hkappa1 hkappa
          (hdomainDist y hy) hcentered hrow hsupportB
          (hgeometry y hy) (hzeroB b y hy) (h143 b y hy)
      simpa [quadraticRate, henergy] using hq
    have hrate :
        ∑ y ∈ D, (quadraticRate y + residualRate y) ≤ potentialRate := by
      dsimp [potentialRate, quadraticRate,
        cmp116Eq220CenteredSourcePotentialRate]
      rw [Finset.sum_add_distrib]
      exact add_le_add_right hresidualRate _
    have hp :=
      cmp116Eq220_re_physicalComplexTauPotential_le_quadratic_add_eq220
        D tau (total sigma psi phi) (residual sigma psi phi)
        (hsmooth sigma psi phi) B
        (∑ ba ∈ cmp116SourcePhysicalLocalizedCoordinates Dict Z0,
          b ba ^ 2)
        potentialRate quadraticRate residualRate domainDist
        E0 epsilon1 C1 alpha4 C2 kappa1 delta kappa M q
        hE0 hepsilon1 hC1 halpha4 hM
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)
        hcentered hquadratic (hresidualCenter b) (h136 b) hrate
    simpa [Cpotential, quadratic,
      cmp116SourcePhysicalComplexTauPotentialCoordinate,
      potentialRate, potentialResidual, S, B] using hp
  have hresult :=
    Cpotential.ae_interactionExponent_le_sourcePhysicalAlpha5_of_potential
      Dict Z0 P threshold sigma tau psi phi conditionedCovariance
      (by simpa [Cpotential] using hroot)
      hpotential
      (by simpa [Cpotential] using hR2)
      hgamma
      (by simpa [potentialRate] using hbudget)
  simpa [Cpotential, quadratic, potentialRate, potentialResidual] using hresult

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
