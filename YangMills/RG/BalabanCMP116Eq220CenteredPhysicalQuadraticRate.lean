/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq220CenteredPotentialQuadraticResidual

/-!
# Physical centered quadratic rate

The centered-contour quadratic estimate used by equation (2.20) is extracted
here as a public producer.  Its hypotheses are the literal radial Hessian
estimate (1.43), exact kernel support, the physical metric budget, and the
uniform exponential row sum.  The conclusion is the precise per-domain
quadratic-rate input consumed by the centered residual compositor.
-/

namespace YangMills.RG

open Matrix
open scoped BigOperators RealInnerProductSpace

noncomputable section

/-- The literal equation-(1.43) Hessian estimate produces the full
center-plus-displacement quadratic rate on a centered Cauchy contour. -/
theorem cmp116Eq220_centeredPhysicalQuadratic_le_rate
    {nY d N Nc : ℕ} [NeZero N]
    (Y0 : Finset (PhysicalBond d N))
    (tau : Fin nY → ℂ)
    (total residual :
      Fin nY → PhysicalGaugeOneCochain d N Nc → ℝ)
    (hsmooth : ∀ y, ContDiff ℝ 2
      (cmp116Eq142PhysicalQuadraticCore total residual y))
    (B : PhysicalGaugeOneCochain d N Nc)
    (kernelSupport :
      Fin nY → PhysicalBond d N → PhysicalBond d N → Prop)
    (domainDist : Fin nY → ℝ) (domainCard : Fin nY → ℕ)
    (E0 epsilon1 C1 alpha4 C3 C2 kappa1 delta kappa : ℝ)
    (M q : ℕ) (rowSum : ℝ) (y : Fin nY)
    (hE0 : 0 < E0) (hepsilon1 : 0 < epsilon1)
    (hC1 : 0 < C1) (halpha4 : 0 < alpha4)
    (hC3 : 0 ≤ C3) (hC3upper : C3 ≤ E0 * C1)
    (hM : 1 ≤ M) (hq : 8 ≤ q) (hkappa1 : 1 < kappa1)
    (hkappa :
      (1 - 3 * delta) * kappa ≤ (1 / 8 : ℝ) * (kappa1 - 1))
    (hdomainDist : 0 ≤ domainDist y)
    (hcentered :
      CMP116Eq214CenteredPolydisc nY
        (fun z =>
          cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
            C2 kappa1 delta kappa (domainDist z))
        tau)
    (hrow : ∀ target : PhysicalBond d N,
      ∑ source : PhysicalBond d N,
        Real.exp (-(cmp116Eq219InternalRate M kappa1 *
          (physicalBondDist target source : ℝ))) ≤ rowSum)
    (hsupportB : ∀ i, i ∉ Y0 → B i = 0)
    (hgeometry : ∀ source target,
      kernelSupport y source target →
        cmp116Eq219InternalRate M kappa1 *
            (physicalBondDist target source : ℝ) ≤
          (1 / 4 : ℝ) * (kappa1 - 1) * domainCard y)
    (hzero : ∀ source target,
      ¬ kernelSupport y source target →
        ∀ (v w : SUNLieCoord Nc), ∀ t ∈ Set.Icc (0 : ℝ) 1,
          cmp116FDerivHessian
            (cmp116Eq142PhysicalQuadraticCore total residual y)
            (t • B)
            (singlePhysicalBondCochain
              (d := d) (N := N) (Nc := Nc) source v)
            (singlePhysicalBondCochain
              (d := d) (N := N) (Nc := Nc) target w) = 0)
    (h143 : ∀ source target (v w : SUNLieCoord Nc),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |cmp116FDerivHessian
          (cmp116Eq142PhysicalQuadraticCore total residual y)
          (t • B)
          (singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) source v)
          (singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) target w)| ≤
          cmp116Eq143QMajorant C3 epsilon1 M C2 kappa1
            (domainDist y) (domainCard y) * ‖v‖ * ‖w‖) :
    ‖tau y‖ *
        |inner ℝ B
          (cmp116Eq142PhysicalSourceQuadratic
            total residual hsmooth y B B)| ≤
      ((cmp116Eq143CenterDomainAmplitude C3 epsilon1 M C2 kappa1
          (domainDist y) (domainCard y) +
        cmp116Eq219DomainAmplitude alpha4 M kappa1 (domainCard y)) *
          rowSum) *
        (∑ i ∈ Y0, ‖B i‖ ^ 2) := by
  obtain ⟨s, hs, htau⟩ := hcentered y
  let radius :=
    cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
      C2 kappa1 delta kappa (domainDist y)
  let Qop :=
    cmp116Eq142PhysicalSourceQuadratic total residual hsmooth y B
  have hradius : 0 ≤ radius := by
    dsimp [radius, cmp116Eq218TauAbsSolved]
    positivity
  have hcenterKernel :
      PhysicalCovarianceExponentialKernelBound Qop physicalBondDist
        (cmp116Eq143CenterDomainAmplitude C3 epsilon1 M C2 kappa1
          (domainDist y) (domainCard y))
        (cmp116Eq219InternalRate M kappa1) := by
    dsimp [Qop]
    exact
      physicalCovarianceExponentialKernelBound_cmp116Eq142PhysicalSourceQuadratic_of_eq143_center
        total residual hsmooth y B physicalBondDist
        (kernelSupport y) C3 epsilon1 C2 kappa1
        (domainDist y) M (domainCard y) hC3 hepsilon1.le hM hkappa1
        hgeometry hzero h143
  have hdisplacementKernel :
      PhysicalCovarianceExponentialKernelBound (radius • Qop)
        physicalBondDist
        (cmp116Eq219DomainAmplitude alpha4 M kappa1 (domainCard y))
        (cmp116Eq219InternalRate M kappa1) := by
    dsimp [radius, Qop]
    apply
      physicalCovarianceExponentialKernelBound_smul_cmp116Eq142PhysicalSourceQuadratic_of_eq143
        total residual hsmooth y B physicalBondDist (kernelSupport y)
        E0 epsilon1 C1 alpha4 C3 C2 kappa1 delta kappa
        (domainDist y) M q (domainCard y)
        hE0 hepsilon1 hC1 halpha4 hC3 hC3upper hM hq hkappa1
    · intro source target hsupp
      apply cmp116Eq219_metricBudget_of_sourceConditions
        hdomainDist hkappa
      simpa [cmp116Eq219InternalRate] using
        hgeometry source target hsupp
    · exact hzero
    · exact h143
  simpa [Qop] using
    (cmp116Eq220_centeredQuadratic_le_localized
      Y0 Qop B (cmp116Eq219InternalRate M kappa1) rowSum
      (cmp116Eq143CenterDomainAmplitude C3 epsilon1 M C2 kappa1
        (domainDist y) (domainCard y))
      (cmp116Eq219DomainAmplitude alpha4 M kappa1 (domainCard y))
      radius hs htau hradius hrow hsupportB hcenterKernel
      hdisplacementKernel)

end

end YangMills.RG
