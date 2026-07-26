/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4RealMixedDerivativeCertificate

/-!
# Exact coordinate affinity of the physical mixed covariance

The source-produced derivative certificate is independent of the value of a
fresh weakening coordinate.  Integrating this literal constant derivative
gives an exact affine identity for the reconstructed physical operator.
This is the source-facing bridge from the convergent random-walk series to a
finite multiaffine polynomial representation.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- A fresh physical weakening coordinate enters the complete mixed
covariance exactly affinely.  The slope is the next mixed covariance and is
constructed from the physical contour series. -/
theorem
    cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative_update_eq_affine
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
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
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (t : ℝ) :
    cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
        (R := R) anchor K hc hmass hK (Function.update s d t) S =
      cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
          (R := R) anchor K hc hmass hK (Function.update s d 0) S +
        t •
          cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
            (R := R) anchor K hc hmass hK s (insert d S) := by
  let curve :=
    cmp116SourcePi4RealMixedCovarianceOperatorCurve
      (R := R) anchor K hc hmass hK s S d
  let slope :=
    cmp116SourcePi4RealMixedCovarianceOperatorDerivative
      (R := R) anchor K hc hmass hK s S d
  have hderiv :
      ∀ u ∈ Set.uIcc (0 : ℝ) t,
        HasDerivAt curve slope u := by
    intro u _hu
    exact
      (CMP116SourcePi4RealMixedDerivativeCertificate.ofPhysicalContour
        anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri hrange
        hΔ hΔ1 s S d hdS hRweak hs hcap hsmall u).hasDerivAt_operator
  have hint :
      IntervalIntegrable (fun _ : ℝ => slope)
        MeasureTheory.volume 0 t :=
    continuous_const.intervalIntegrable 0 t
  have hFTC :
      (t - 0) • slope = curve t - curve 0 := by
    rw [← intervalIntegral.integral_const slope]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have haffine :
      curve t = curve 0 + t • slope := by
    calc
      curve t = (curve t - curve 0) + curve 0 :=
        (sub_add_cancel _ _).symm
      _ = (t - 0) • slope + curve 0 := by rw [← hFTC]
      _ = curve 0 + t • slope := by
        simp [add_comm]
  simpa [curve, slope,
    cmp116SourcePi4RealMixedCovarianceOperatorCurve_eq,
    cmp116SourcePi4RealMixedCovarianceOperatorDerivative_eq] using haffine

end

end YangMills.RG
