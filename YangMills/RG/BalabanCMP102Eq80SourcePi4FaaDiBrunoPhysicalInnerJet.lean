/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4FaaDiBruno
import YangMills.RG.BalabanCMP116SourcePi4RealMixedCovarianceVertexInterpolation

/-!
# Physical inner jet for the equation-(80) Faà di Bruno formula

The arbitrary-depth composition formula contains derivatives of the smooth
finite vertex interpolant.  This file identifies its first Taylor
coefficient in a canonical weakening-coordinate direction with the literal
next source-produced mixed covariance.

The equality is obtained from the physical contour derivative theorem and
uniqueness of the derivative of the same one-dimensional coordinate curve.
It is not a formal finite-difference definition of the jet.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

set_option maxHeartbeats 5000000 in
/-- The Fréchet derivative of the mixed-covariance vertex polynomial in one
fresh canonical coordinate is the next physical mixed covariance. -/
theorem
    fderiv_cmp116FiniteMultiaffineInterpolation_sourcePi4FullRealMixedCovariance_apply_single
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
    (L : List (FinBox 4 (2 * Q))) (hL : L.Nodup)
    (hfresh : ∀ e ∈ L, e ∉ S)
    (d : FinBox 4 (2 * Q)) (hdL : d ∈ L)
    (hRweak : 1 ≤ Rweak)
    (hsShift : ∀ x, ‖(s x : ℂ) - 1‖ ≤ (1 : ℝ))
    (hsCap : ∀ x, ‖(s x : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1) :
    fderiv ℝ
        (cmp116FiniteMultiaffineInterpolation
          (fun sigma =>
            cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
              (R := R) anchor K hc hmass hK sigma S)
          s L)
        s (Pi.single d 1) =
      cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
        (R := R) anchor K hc hmass hK s (insert d S) := by
  let P :=
    cmp116FiniteMultiaffineInterpolation
      (fun sigma =>
        cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
          (R := R) anchor K hc hmass hK sigma S)
      s L
  have hP :
      DifferentiableAt ℝ P (Function.update s d (s d)) :=
    (contDiff_cmp116FiniteMultiaffineInterpolation
      1
      (fun sigma =>
        cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
          (R := R) anchor K hc hmass hK sigma S)
      s L).differentiable one_ne_zero _
  have hcurve :=
    hasDerivAt_cmp116FiniteMultiaffineInterpolation_sourcePi4FullRealMixedCovariance
      anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri
      hrange hΔ hΔ1 s S L hL hfresh d hdL hRweak hsShift hsCap
      hsmall (s d)
  have hchain :
      HasDerivAt
        (fun u => P (Function.update s d u))
        (fderiv ℝ P s (Pi.single d 1)) (s d) := by
    have h :=
      hP.hasFDerivAt.comp_hasDerivAt (s d)
        (hasDerivAt_update s d (s d))
    simpa [Function.comp_def] using h
  exact hchain.unique hcurve

set_option maxHeartbeats 5000000 in
/-- The order-one Taylor coefficient used by Faà di Bruno is therefore the
literal next physical mixed covariance. -/
theorem
    ftaylorSeries_cmp116FiniteMultiaffineInterpolation_sourcePi4FullRealMixedCovariance_one_apply_single
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
    (L : List (FinBox 4 (2 * Q))) (hL : L.Nodup)
    (hfresh : ∀ e ∈ L, e ∉ S)
    (d : FinBox 4 (2 * Q)) (hdL : d ∈ L)
    (hRweak : 1 ≤ Rweak)
    (hsShift : ∀ x, ‖(s x : ℂ) - 1‖ ≤ (1 : ℝ))
    (hsCap : ∀ x, ‖(s x : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1) :
    ftaylorSeries ℝ
        (cmp116FiniteMultiaffineInterpolation
          (fun sigma =>
            cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
              (R := R) anchor K hc hmass hK sigma S)
          s L)
        s 1 (fun _ => Pi.single d 1) =
      cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
        (R := R) anchor K hc hmass hK s (insert d S) := by
  simpa [ftaylorSeries] using
    fderiv_cmp116FiniteMultiaffineInterpolation_sourcePi4FullRealMixedCovariance_apply_single
      anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri
      hrange hΔ hΔ1 s S L hL hfresh d hdL hRweak hsShift hsCap hsmall

end

end YangMills.RG
