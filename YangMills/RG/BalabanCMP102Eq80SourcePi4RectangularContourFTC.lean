/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4RectangularContourDerivative
import YangMills.RG.BalabanCMP99RectangularMinimizerAnalyticFTC

/-!
# One-coordinate FTC for rectangular CMP102 equation (80)

The source contour produces a continuously differentiable physical
rectangular minimizer.  This module consumes that fact in the literal four
terms of equation (80).  The derivative of `V₀` is evaluated at the actual
shifted field, and continuity of the complete derivative is generated from
`C¹` regularity of `V₀`; interval integrability is not a caller premise.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

/-- Continuity on a set of the exact equation-(80) directional derivative
when both the rectangular propagator and its derivative vary. -/
theorem
    continuousOn_cmp102Eq80PropagatorDirectionalDerivative_families
    {X E F : Type*}
    [TopologicalSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D D₃ : E → F) (V₀ : E → ℝ)
    (Hfamily Kfamily : X → F →L[ℝ] E)
    (Δπ : E →L[ℝ] E) (J A : E)
    (s : Set X)
    (hH : ContinuousOn Hfamily s)
    (hK : ContinuousOn Kfamily s)
    (hV₀ : Continuous (fderiv ℝ V₀)) :
    ContinuousOn
      (fun x =>
        cmp102Eq80PropagatorDirectionalDerivative D D₃
          (Hfamily x) (Kfamily x) Δπ J A
          (fderiv ℝ V₀ (A - Hfamily x (D A)))) s := by
  have hHD : ContinuousOn (fun x => Hfamily x (D A)) s :=
    hH.clm_apply continuousOn_const
  have hKD : ContinuousOn (fun x => Kfamily x (D A)) s :=
    hK.clm_apply continuousOn_const
  have hKD₃ : ContinuousOn (fun x => Kfamily x (D₃ A)) s :=
    hK.clm_apply continuousOn_const
  have harg : ContinuousOn (fun x => A - Hfamily x (D A)) s :=
    continuousOn_const.sub hHD
  have hVderiv : ContinuousOn
      (fun x => fderiv ℝ V₀ (A - Hfamily x (D A))) s :=
    hV₀.comp_continuousOn harg
  have hVapply : ContinuousOn
      (fun x =>
        fderiv ℝ V₀ (A - Hfamily x (D A)) (Kfamily x (D A))) s :=
    hVderiv.clm_apply hKD
  have hΔHD : ContinuousOn
      (fun x => Δπ (Hfamily x (D A))) s :=
    continuousOn_const.clm_apply hHD
  have hΔKD : ContinuousOn
      (fun x => Δπ (Kfamily x (D A))) s :=
    continuousOn_const.clm_apply hKD
  unfold cmp102Eq80PropagatorDirectionalDerivative
  fun_prop

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

set_option maxHeartbeats 12000000 in
/-- The literal rectangular equation-(80) potential satisfies one-coordinate
FTC on the complete source segment.  Coarse nonsingularity, the minimizer
derivative, and interval integrability are all generated internally. -/
theorem
    integral_cmp102Eq80SourcePi4RectangularContourPotentialDerivative_eq_sub_of_source
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
    (hD :
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
    (hradius : 1 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hsigma : ∀ x, ‖sigma x - 1‖ ≤ (1 : ℝ))
    (hcap : ∀ x, ‖sigma x‖ ≤ Rweak)
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
    (hV₀ : ContDiff ℝ 1 V₀) :
    (∫ t : ℝ in (0 : ℝ)..1,
        cmp102Eq80SourcePi4RectangularContourPotentialDerivative
          (R := R) anchor K hc hmass hK D D₃ Δπ J sigma d A t
          (fderiv ℝ V₀
            (A -
              cmp99SourcePi4RealBackgroundMinimizerOperatorCurve
                (R := R) anchor K hc hmass hK sigma d t (D A)))) =
      cmp102Eq80SourcePi4RectangularContourPotentialCurve
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J sigma d A 1 -
        cmp102Eq80SourcePi4RectangularContourPotentialCurve
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J sigma d A 0 := by
  let Hcurve :=
    cmp99SourcePi4RealBackgroundMinimizerOperatorCurve
      (R := R) anchor K hc hmass hK sigma d
  let Kcurve :=
    cmp99SourcePi4RealBackgroundMinimizerOperatorDerivative
      (R := R) anchor K hc hmass hK sigma d
  have hsegmentDeriv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt Hcurve (Kcurve t) t := by
    intro t ht
    exact
      hasDerivAt_cmp99SourcePi4RealBackgroundMinimizerOperatorCurve_of_source
        anchor K hsourceRange hfiniteRange hc hmass hK hD
        hcoarseRate hcoarse hAhead hrho hrate hgeom Cert htri hΔ hΔ1
        sigma d (show 0 ≤ radius by linarith) hRweak hsigma hcap t
        (sourceUpdate_unitShifted sigma d hsigma hradius ht)
        (sourceUpdate_cap sigma d hRweak hcap ht)
        hcontourSmall hcoarseSmall
  have hHcontinuous : ContinuousOn Hcurve (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    exact (hsegmentDeriv t ht).continuousAt.continuousWithinAt
  have hKcontinuous : ContinuousOn Kcurve (Set.Icc (0 : ℝ) 1) := by
    apply
      continuousOn_cmp99PhysicalRectangularOfComplexMatrix_of_entrywise
    intro row col
    exact
      continuousOn_cmp99SourcePi4BackgroundMinimizerDerivative_compOfReal_of_source
        anchor K hsourceRange hfiniteRange hc hmass hK hD
        hcoarseRate hcoarse hAhead hrho hrate hgeom Cert htri hΔ hΔ1
        sigma d hradius hRweak hsigma hcap hcontourSmall hcoarseSmall
        row col
  let derivativeCurve := fun t : ℝ =>
    cmp102Eq80PropagatorDirectionalDerivative D D₃
      (Hcurve t) (Kcurve t) Δπ J A
      (fderiv ℝ V₀ (A - Hcurve t (D A)))
  have hDerivativeContinuous :
      ContinuousOn derivativeCurve (Set.Icc (0 : ℝ) 1) := by
    exact
      continuousOn_cmp102Eq80PropagatorDirectionalDerivative_families
        D D₃ V₀ Hcurve Kcurve Δπ J A
        (Set.Icc (0 : ℝ) 1) hHcontinuous hKcontinuous
        (hV₀.continuous_fderiv one_ne_zero)
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := cmp102Eq80SourcePi4RectangularContourPotentialCurve
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J sigma d A)
    (f' := derivativeCurve)
  · intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    have hV₀At :
        HasFDerivAt V₀
          (fderiv ℝ V₀ (A - Hcurve t (D A)))
          (A - Hcurve t (D A)) :=
      (hV₀.differentiable one_ne_zero
        (A - Hcurve t (D A))).hasFDerivAt
    exact
      hasDerivAt_cmp102Eq80SourcePi4RectangularContourPotential
        anchor K hc hmass hK D D₃ V₀ Δπ J sigma d A t
        (hsegmentDeriv t htIcc)
        (fderiv ℝ V₀ (A - Hcurve t (D A))) hV₀At
  · have hcontinuous' : ContinuousOn derivativeCurve
        (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        hDerivativeContinuous
    simpa [derivativeCurve, Hcurve, Kcurve,
      cmp102Eq80SourcePi4RectangularContourPotentialDerivative] using
      hcontinuous'.intervalIntegrable

end

end YangMills.RG
