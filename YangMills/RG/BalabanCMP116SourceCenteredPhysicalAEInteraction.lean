/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq220CenteredSourcePotential
import YangMills.RG.BalabanCMP116SourcePhysicalAEInteraction

/-!
# Source-faithful AE interaction on centered source contours

The source contour in CMP116 is centered at its interpolation parameter.
This module connects the literal radial Hessian estimate `(1.43)` and
residual estimate `(1.36)` to the almost-everywhere `alpha5` interaction
bound without replacing either estimate by a uniform bound on the full
shifted source coordinate.
-/

namespace YangMills.RG

open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.Operator

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- The complete localized quadratic coefficient on a centered source
contour: the first term is the interpolation-center cost and the second is
the contour-displacement cost of `(2.19)`. -/
noncomputable def cmp116Eq220CenteredSourcePotentialRate
    {nY : ℕ} (D : Finset (Fin nY))
    (domainDist : Fin nY → ℝ) (domainCard : Fin nY → ℕ)
    (C3 epsilon1 : ℝ) (M : ℕ) (C2 kappa1 alpha4 rowSum : ℝ) : ℝ :=
  ∑ y ∈ D,
    (cmp116Eq143CenterDomainAmplitude C3 epsilon1 M C2 kappa1
        (domainDist y) (domainCard y) +
      cmp116Eq219DomainAmplitude alpha4 M kappa1 (domainCard y)) *
        rowSum

/-- The complete centered-source residual ledger: the first term is the
literal center value from `(1.36)` and the second is its contour displacement
after the source radius `(2.18)` is consumed. -/
noncomputable def cmp116Eq220CenteredSourceResidual
    {nY : ℕ} (D : Finset (Fin nY))
    (domainDist : Fin nY → ℝ)
    (E0 epsilon1 C1 : ℝ) (M q : ℕ)
    (C2 kappa1 delta kappa alpha4 : ℝ) : ℝ :=
  ∑ y ∈ D,
    (cmp116Eq136ResidualMajorant E0 epsilon1 C1 M q
        C2 kappa1 delta kappa (domainDist y) +
      cmp116Eq220ResidualDomainWeight alpha4 delta kappa
        (domainDist y))

/-- Per-domain form of the centered source residual ledger. -/
noncomputable def cmp116Eq220CenteredSourceResidualWeight
    {nY : ℕ} (domainDist : Fin nY → ℝ)
    (E0 epsilon1 C1 : ℝ) (M q : ℕ)
    (C2 kappa1 delta kappa alpha4 : ℝ) (y : Fin nY) : ℝ :=
  cmp116Eq136ResidualMajorant E0 epsilon1 C1 M q
      C2 kappa1 delta kappa (domainDist y) +
    cmp116Eq220ResidualDomainWeight alpha4 delta kappa
      (domainDist y)

theorem cmp116Eq220CenteredSourceResidual_eq_sum_weight
    {nY : ℕ} (D : Finset (Fin nY))
    (domainDist : Fin nY → ℝ)
    (E0 epsilon1 C1 : ℝ) (M q : ℕ)
    (C2 kappa1 delta kappa alpha4 : ℝ) :
    cmp116Eq220CenteredSourceResidual D domainDist
        E0 epsilon1 C1 M q C2 kappa1 delta kappa alpha4 =
      ∑ y ∈ D,
        cmp116Eq220CenteredSourceResidualWeight domainDist
          E0 epsilon1 C1 M q C2 kappa1 delta kappa alpha4 y := by
  rfl

/-- Positivity of the centered residual is generated from the positive source
normalizations; no independent sign hypothesis is needed downstream. -/
theorem cmp116Eq220CenteredSourceResidualWeight_nonneg
    {nY : ℕ} (domainDist : Fin nY → ℝ)
    {E0 epsilon1 C1 : ℝ} {M q : ℕ}
    {C2 kappa1 delta kappa alpha4 : ℝ}
    (hE0 : 0 ≤ E0) (hepsilon1 : 0 ≤ epsilon1)
    (hC1 : 0 ≤ C1) (halpha4 : 0 ≤ alpha4)
    (y : Fin nY) :
    0 ≤ cmp116Eq220CenteredSourceResidualWeight domainDist
      E0 epsilon1 C1 M q C2 kappa1 delta kappa alpha4 y := by
  unfold cmp116Eq220CenteredSourceResidualWeight
    cmp116Eq136ResidualMajorant cmp116Eq220ResidualDomainWeight
  positivity

namespace CMP116Eq214PhysicalContourDensity

set_option maxHeartbeats 4000000 in
/-- Literal `(1.43)` and `(1.36)` on a centered source contour produce the
AE equation-`(2.20)`--`(2.22)` interaction estimate.  The radial Taylor
operator, localized potential rate, and residual ledger are all generated
inside the theorem. -/
theorem ae_interactionExponent_le_sourcePhysicalAlpha5_of_centeredSource
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
          (1 / 4 : ℝ) * (kappa1 - 1) *
            ((M : ℝ) ^ 4)⁻¹ * domainCard y)
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
    (h136 : ∀ b y, y ∈ D →
      |residual sigma psi phi y
        (physicalBondProjection
          (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
          (cmp116SourcePhysicalCoordinateCochain b))| ≤
        cmp116Eq136ResidualMajorant E0 epsilon1 C1 M q
          C2 kappa1 delta kappa (domainDist y))
    {r2Rate gamma alpha : ℝ}
    (hR2 :
      (‖C.r2Matrix sigma tau psi phi‖ +
        ‖(C.r2Matrix sigma tau psi phi).transpose‖) / 2 ≤ r2Rate)
    (hgamma : 0 ≤ gamma)
    (hbudget :
      cmp116Eq220CenteredSourcePotentialRate D domainDist domainCard
          C3 epsilon1 M C2 kappa1 alpha4 rowSum +
        r2Rate + gamma ≤ alpha) :
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
          cmp116Eq220CenteredSourceResidual D domainDist
            E0 epsilon1 C1 M q C2 kappa1 delta kappa alpha4 := by
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
  let potentialRate :=
    cmp116Eq220CenteredSourcePotentialRate D domainDist domainCard
      C3 epsilon1 M C2 kappa1 alpha4 rowSum
  let potentialResidual :=
    cmp116Eq220CenteredSourceResidual D domainDist
      E0 epsilon1 C1 M q C2 kappa1 delta kappa alpha4
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
    have hp :=
      cmp116Eq220_re_physicalComplexTauPotential_le_centeredSource
        D S tau (total sigma psi phi) (residual sigma psi phi)
        (hsmooth sigma psi phi) B kernelSupport domainDist domainCard
        E0 epsilon1 C1 alpha4 C3 C2 kappa1 delta kappa M q rowSum
        hE0 hepsilon1 hC1 halpha4 hC3 hC3upper hM hq hkappa1 hkappa
        hdomainDist hcentered hrow hsupportB hgeometry
        (hzeroB b) (h143 b) (h136 b)
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
    simpa [Cpotential, quadratic,
      cmp116SourcePhysicalComplexTauPotentialCoordinate,
      potentialRate, potentialResidual, S, B, henergy] using hp
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
