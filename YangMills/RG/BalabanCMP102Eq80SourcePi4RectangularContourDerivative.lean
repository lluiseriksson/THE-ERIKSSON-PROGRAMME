/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PropagatorDerivative
import YangMills.RG.BalabanCMP99PhysicalRectangularComplexCurve

/-!
# Weakening derivative of equation (80) with the rectangular minimizer

This is the source-faithful replacement for the earlier square-covariance
curve.  CMP102 equation (80) is evaluated on

`H(u) = C(u) Q* (Q C(u) Q*)⁻¹ : F → E`,

and its derivative is the physical rectangular derivative reconstructed
from the complete complex contour.  The four terms of equation (80) are
then differentiated by the existing exact propagator chain rule.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

private abbrev FineEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FineField M Q Nc →L[ℝ] FineField M Q Nc

/-- Literal equation-(80) potential along the real restriction of the
rectangular complex minimizer contour. -/
noncomputable def
    cmp102Eq80SourcePi4RectangularContourPotentialCurve
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (Δπ : FineEndomorphism M Q Nc)
    (J : FineField M Q Nc)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (d : FinBox 4 (2 * Q))
    (A : FineField M Q Nc)
    (u : ℝ) : ℝ :=
  cmp102Eq80GlobalPotential D D₃ V₀
    (cmp99SourcePi4RealBackgroundMinimizerOperatorCurve
      (R := R) anchor K hc hmass hK sigma d u)
    Δπ J A

/-- Exact directional derivative of the rectangular equation-(80)
potential at one weakening coordinate. -/
noncomputable def
    cmp102Eq80SourcePi4RectangularContourPotentialDerivative
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (Δπ : FineEndomorphism M Q Nc)
    (J : FineField M Q Nc)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (d : FinBox 4 (2 * Q))
    (A : FineField M Q Nc)
    (t : ℝ)
    (V₀' : FineField M Q Nc →L[ℝ] ℝ) : ℝ :=
  cmp102Eq80PropagatorDirectionalDerivative D D₃
    (cmp99SourcePi4RealBackgroundMinimizerOperatorCurve
      (R := R) anchor K hc hmass hK sigma d t)
    (cmp99SourcePi4RealBackgroundMinimizerOperatorDerivative
      (R := R) anchor K hc hmass hK sigma d t)
    Δπ J A V₀'

/-- Once the physical minimizer derivative is generated, the exact
equation-(80) derivative follows without an additional estimate. -/
theorem
    hasDerivAt_cmp102Eq80SourcePi4RectangularContourPotential
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (Δπ : FineEndomorphism M Q Nc)
    (J : FineField M Q Nc)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (d : FinBox 4 (2 * Q))
    (A : FineField M Q Nc)
    (t : ℝ)
    (hH : HasDerivAt
      (cmp99SourcePi4RealBackgroundMinimizerOperatorCurve
        (R := R) anchor K hc hmass hK sigma d)
      (cmp99SourcePi4RealBackgroundMinimizerOperatorDerivative
        (R := R) anchor K hc hmass hK sigma d t) t)
    (V₀' : FineField M Q Nc →L[ℝ] ℝ)
    (hV₀ : HasFDerivAt V₀ V₀'
      (A -
        cmp99SourcePi4RealBackgroundMinimizerOperatorCurve
          (R := R) anchor K hc hmass hK sigma d t (D A))) :
    HasDerivAt
      (cmp102Eq80SourcePi4RectangularContourPotentialCurve
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J sigma d A)
      (cmp102Eq80SourcePi4RectangularContourPotentialDerivative
        (R := R) anchor K hc hmass hK D D₃ Δπ J sigma d A t V₀') t := by
  unfold cmp102Eq80SourcePi4RectangularContourPotentialCurve
    cmp102Eq80SourcePi4RectangularContourPotentialDerivative
  exact
    hasDerivAt_cmp102Eq80GlobalPotential_propagatorCurve
      D D₃ V₀
      (cmp99SourcePi4RealBackgroundMinimizerOperatorCurve
        (R := R) anchor K hc hmass hK sigma d)
      (cmp99SourcePi4RealBackgroundMinimizerOperatorDerivative
        (R := R) anchor K hc hmass hK sigma d t)
      Δπ J A t hH V₀' hV₀

set_option maxHeartbeats 5000000 in
/-- Complete source contour data generate the derivative of the literal
rectangular equation-(80) potential.  Neither a minimizer derivative nor a
coarse determinant is supplied by the caller. -/
theorem
    hasDerivAt_cmp102Eq80SourcePi4RectangularContourPotential_of_source
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hfiniteRange : PhysicalCovarianceFiniteRange
      K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hPatchDefect :
      ‖cmp99PatchedPhysicalParametrixDefect
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          hc hmass hK‖ < 1)
    {coarseRate : ℝ} (hcoarseRate : 0 < coarseRate)
    (hcoarse : IsCoerciveCLM
      (cmp99SourcePi4WeakenedCoarseMiddle
        (R := R) anchor K hc hmass hK (fun _ => 1)) coarseRate)
    {Ahead rho rate radius Rweak : ℝ}
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
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (d : FinBox 4 (2 * Q))
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hsigma : ∀ x, ‖sigma x - 1‖ ≤ (1 : ℝ))
    (hcap : ∀ x, ‖sigma x‖ ≤ Rweak)
    (t : ℝ)
    (hdiffUpdate :
      ∀ x, ‖Function.update sigma d (t : ℂ) x - 1‖ ≤ radius)
    (hcapUpdate :
      ∀ x, ‖Function.update sigma d (t : ℂ) x‖ ≤ Rweak)
    (hcontourSmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hcoarseSmall :
      cmp99SourcePi4ComplexCoarseRelativeDefectBound
        (M := M) (Q := Q) (Nc := Nc)
        (cmp99SourcePi4WeakenedCoarseCovariance
          (R := R) anchor K hc hmass hK (fun _ => 1)
          hcoarseRate hcoarse)
        Δ Ahead rho rate radius Rweak < 1)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (Δπ : FineEndomorphism M Q Nc)
    (J A : FineField M Q Nc)
    (V₀' : FineField M Q Nc →L[ℝ] ℝ)
    (hV₀ : HasFDerivAt V₀ V₀'
      (A -
        cmp99SourcePi4RealBackgroundMinimizerOperatorCurve
          (R := R) anchor K hc hmass hK sigma d t (D A))) :
    HasDerivAt
      (cmp102Eq80SourcePi4RectangularContourPotentialCurve
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J sigma d A)
      (cmp102Eq80SourcePi4RectangularContourPotentialDerivative
        (R := R) anchor K hc hmass hK D D₃ Δπ J sigma d A t V₀') t := by
  have hH :=
    hasDerivAt_cmp99SourcePi4RealBackgroundMinimizerOperatorCurve_of_source
      anchor K hsourceRange hfiniteRange hc hmass hK hPatchDefect
      hcoarseRate hcoarse hAhead hrho hrate hgeom Cert htri hΔ hΔ1
      sigma d hradius hRweak hsigma hcap t hdiffUpdate hcapUpdate
      hcontourSmall hcoarseSmall
  exact
    hasDerivAt_cmp102Eq80SourcePi4RectangularContourPotential
      anchor K hc hmass hK D D₃ V₀ Δπ J sigma d A t
      hH V₀' hV₀

end

end YangMills.RG
