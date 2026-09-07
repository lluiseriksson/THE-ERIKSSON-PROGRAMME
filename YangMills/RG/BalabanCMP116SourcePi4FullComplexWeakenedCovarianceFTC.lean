/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Analysis.Complex.RealDeriv
import YangMills.RG.BalabanCMP116FTCInterpolation
import YangMills.RG.BalabanCMP116SourcePi4FullComplexWeakenedCovarianceDerivativeSeries

/-!
# Physical one-coordinate FTC for the complete weakened covariance

This module consumes the source `Pi^4` derivative-series theorem in the real
weakening interpolation used by CMP116.  The result is an actual
fundamental-theorem-of-calculus identity for the complete, length-ordered
physical covariance; it is not an endpoint Möbius replacement.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- One literal real FTC step for a physical weakening coordinate of the
complete complex covariance. -/
theorem cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_update_zero_add_integral_derivative
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate Rweak : ℝ}
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
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (d : FinBox 4 (2 * Q))
    (hRweak : 1 ≤ Rweak)
    (hsigma : ∀ x, ‖sigma x - 1‖ ≤ (1 : ℝ))
    (hcap : ∀ x, ‖sigma x‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc) :
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
          (R := R) anchor K hc hmass hK
          (Function.update sigma d 0) row col +
        ∫ _t in (0 : ℝ)..1,
          cmp116SourcePi4FullComplexWeakenedCovarianceMatrixDerivative
            (R := R) anchor K hc hmass hK sigma d row col =
      cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
        (R := R) anchor K hc hmass hK
        (Function.update sigma d 1) row col := by
  letI : ContinuousSMul ℝ ℂ := {
    continuous_smul := by
      simpa [Complex.real_smul] using
        (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd
  }
  let curve : ℝ → ℂ := fun t =>
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
      (R := R) anchor K hc hmass hK
      (Function.update sigma d (t : ℂ)) row col
  let derivative : ℝ → ℂ := fun _ =>
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrixDerivative
      (R := R) anchor K hc hmass hK sigma d row col
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt curve (derivative t) t := by
    intro t _
    exact
      (hasDerivAt_cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_update
        anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
        hΔ hΔ1 sigma d hRweak hsigma hcap hsmall row col (t : ℂ)).comp_ofReal
  have hint : IntervalIntegrable derivative MeasureTheory.volume 0 1 :=
    continuous_const.intervalIntegrable 0 1
  simpa [curve, derivative] using
    (cmp116FTC_oneStep curve derivative hderiv hint)

end

end YangMills.RG
