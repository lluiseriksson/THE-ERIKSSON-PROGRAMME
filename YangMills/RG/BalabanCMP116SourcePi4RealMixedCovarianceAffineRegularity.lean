/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4RealMixedCovarianceAffine

/-!
# All-order regularity of the physical covariance coordinate lines

The exact affine identity for a fresh weakening coordinate immediately
upgrades the source-produced `C¹` contour theorem to `C∞`: the complete
physical mixed covariance is a literal affine line with the next mixed
covariance as its constant slope.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- Every source-certified fresh-coordinate covariance curve is smooth to
arbitrary order.  This is derived from its exact affine representation, not
assumed as an analytic interface. -/
theorem
    contDiff_cmp116SourcePi4RealMixedCovarianceOperatorCurve_ofPhysicalContour
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (n : WithTop ℕ∞)
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (PatchCert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (s : FinBox 4 (2 * Q) → ℝ)
    (S : Finset (FinBox 4 (2 * Q)))
    (d : FinBox 4 (2 * Q)) (hdS : d ∉ S)
    (hRweak : 1 ≤ Rweak)
    (hs : ∀ x, ‖(s x : ℂ) - 1‖ ≤ (1 : ℝ))
    (hcap : ∀ x, ‖(s x : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1) :
    ContDiff ℝ n
      (cmp116SourcePi4RealMixedCovarianceOperatorCurve
        (R := R) anchor K hc hmass hK s S d) := by
  let H₀ :=
    cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
      (R := R) anchor K hc hmass hK (Function.update s d 0) S
  let slope :=
    cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
      (R := R) anchor K hc hmass hK s (insert d S)
  have hcurve :
      cmp116SourcePi4RealMixedCovarianceOperatorCurve
          (R := R) anchor K hc hmass hK s S d =
        fun t : ℝ => H₀ + t • slope := by
    funext t
    rw [cmp116SourcePi4RealMixedCovarianceOperatorCurve_eq]
    exact
      cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative_update_eq_affine
        anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri hrange
        hΔ hΔ1 s S d hdS hRweak hs hcap hsmall t
  rw [hcurve]
  exact contDiff_const.add
    ((contDiff_id : ContDiff ℝ n (fun t : ℝ => t)).smul contDiff_const)

end

end YangMills.RG
