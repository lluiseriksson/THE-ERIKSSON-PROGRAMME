/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq249CentralStabilizedComplexFloor

/-!
# Positive scalar radius for the stabilized CMP89 complex floor

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the compiler.

All three scalar strip budgets used below are continuous in `rho`. At
`rho = 0`, the amplitude and noncentral-gap left sides vanish, as does the
complete stabilized-denominator variation, while the real stabilized floor
is strictly positive for `a > 0`. Hence one common positive radius satisfies
the three conservative conditions already sealed in the tree.

This proves non-vacuity of the scalar strip regime; it deliberately does not
choose an optimized numerical radius. The sharper trigonometric gap and the
proposed factor-two opposite-pair variation are not used. The flowing source
condition `mass^2 <= 1`, construction of the complete complex integrand,
contour displacement, the Fourier/physical rate dictionary and window 15
remain separate.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- The complete stabilized variation majorant is continuous at zero strip
width. All infinite alias sums occurring here are fixed constants; only their
explicit elementary prefactors depend on `rho`. -/
theorem continuousAt_cmp89Eq249CentralStabilizedDenominatorVariationBound
    (a : ℝ) :
    ContinuousAt
      (fun rho =>
        cmp89Eq249CentralStabilizedDenominatorVariationBound a rho) 0 := by
  unfold cmp89Eq249CentralStabilizedDenominatorVariationBound
    cmp89Eq249CentralFineSymbolVerticalBound
    cmp89Eq249CentralAveragePairVerticalBound
    cmp89Eq249ComplexNoncentralAliasSumBound
    cmp89Eq249ComplexNoncentralAliasQuotientConstant
    cmp89Eq249ComplexNoncentralAliasRadialConstant
    cmp89Eq249ComplexNoncentralAliasSumVariationBound
    cmp89Eq249ComplexNoncentralAliasQuotientVariationConstant
    cmp89Eq249ComplexNoncentralAliasQuotientVariationRadialConstant
    cmp89Eq248ComplexAliasPairVerticalConstant
    cmp89Eq248ComplexAliasPairStripConstant
    cmp89Eq245EntireAverageAliasStripConstant
  fun_prop

/-- Every explicit vertical contribution vanishes at zero strip width. -/
theorem cmp89Eq249CentralStabilizedDenominatorVariationBound_zero
    (a : ℝ) :
    cmp89Eq249CentralStabilizedDenominatorVariationBound a 0 = 0 := by
  simp [cmp89Eq249CentralStabilizedDenominatorVariationBound,
    cmp89Eq249CentralFineSymbolVerticalBound,
    cmp89Eq249CentralAveragePairVerticalBound,
    cmp89Eq249ComplexNoncentralAliasSumVariationBound,
    cmp89Eq249ComplexNoncentralAliasQuotientVariationConstant,
    cmp89Eq249ComplexNoncentralAliasQuotientVariationRadialConstant,
    cmp89Eq248ComplexAliasPairVerticalConstant]

/-- For every positive averaging coefficient there is one positive strip
radius satisfying all three conservative scalar conditions simultaneously. -/
theorem exists_cmp89Eq249CentralStabilizedComplexRadius
    {a : ℝ} (ha : 0 < a) :
    ∃ rho : ℝ, 0 < rho ∧
      rho * Real.exp rho ≤ 1 / 6 ∧
      CMP89Eq249UniformNoncentralComplexRadiusCondition rho ∧
      CMP89Eq249CentralStabilizedComplexWindow a rho := by
  let amplitude : ℝ → ℝ := fun rho => rho * Real.exp rho
  let gapLhs : ℝ → ℝ := fun rho =>
    let eps := rho * Real.exp rho
    eps * (4 * Real.pi + 4 * eps)
  let gapRhs : ℝ := ((1 / (3 * Real.pi)) ^ 2 * Real.pi ^ 2) / 2
  let variation : ℝ → ℝ := fun rho =>
    cmp89Eq249CentralStabilizedDenominatorVariationBound a rho
  let floor : ℝ := cmp89Eq249CentralStabilizedLowerConstant 4 a
  have hfloorPos : 0 < floor := by
    rw [floor, cmp89Eq249CentralStabilizedLowerConstant]
    positivity
  have hgapRhsPos : 0 < gapRhs := by
    dsimp [gapRhs]
    positivity
  have hampCont : ContinuousAt amplitude 0 := by
    dsimp [amplitude]
    fun_prop
  have hgapCont : ContinuousAt gapLhs 0 := by
    dsimp [gapLhs]
    fun_prop
  have hvariationCont : ContinuousAt variation 0 := by
    simpa [variation] using
      continuousAt_cmp89Eq249CentralStabilizedDenominatorVariationBound a
  have hampEventually : ∀ᶠ rho in 𝓝 (0 : ℝ), amplitude rho < 1 / 6 := by
    have h := hampCont.eventually
      (eventually_lt_nhds (by norm_num : amplitude 0 < 1 / 6))
    exact h
  have hgapEventually : ∀ᶠ rho in 𝓝 (0 : ℝ), gapLhs rho < gapRhs := by
    have hzero : gapLhs 0 = 0 := by simp [gapLhs]
    have h := hgapCont.eventually
      (eventually_lt_nhds (by simpa [hzero] using hgapRhsPos))
    exact h
  have hvariationEventually :
      ∀ᶠ rho in 𝓝 (0 : ℝ), variation rho < floor := by
    have hzero : variation 0 = 0 := by
      simpa [variation] using
        cmp89Eq249CentralStabilizedDenominatorVariationBound_zero a
    have h := hvariationCont.eventually
      (eventually_lt_nhds (by simpa [hzero] using hfloorPos))
    exact h
  rcases
      (hampEventually.and (hgapEventually.and hvariationEventually)).exists_gt
      with ⟨rho, hrho, hamp, hgap, hvariation⟩
  refine ⟨rho, hrho, hamp.le, ?_, ?_⟩
  · simpa [CMP89Eq249UniformNoncentralComplexRadiusCondition, gapLhs, gapRhs]
      using hgap.le
  · simpa [CMP89Eq249CentralStabilizedComplexWindow, variation, floor]
      using hvariation

end

end YangMills.RG
