/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import YangMills.RG.BalabanCMP102Eq80PropagatorDerivative

/-!
# Ordered minimizer telescoping for CMP102 equation (80)

The equation-(80) potential is nonlinear in the rectangular minimizer.
Consequently, a convergent walk expansion of the minimizer cannot simply be
passed termwise through the potential.  This module gives the exact finite
ordered replacement: add one minimizer term at a time and telescope the
literal four-term potential.

No infinite sums are exchanged.  No connectivity is asserted for an
isolated minimizer term.  The anchor-dependent potential and the new walk
term first meet inside one exact increment; localization belongs at that
level.
-/

open scoped RealInnerProductSpace

namespace YangMills.RG

noncomputable section

open MeasureTheory

/-- Exact change of the CMP102 equation-(80) potential when a rectangular
minimizer `T` is added after a prefix `P`.  The quadratic cross terms and
the nonlinear `V₀` difference remain literal. -/
noncomputable def cmp102Eq80MinimizerIncrement
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D D₃ : E → F) (V₀ : E → ℝ)
    (P T : F →L[ℝ] E) (Δπ : E →L[ℝ] E)
    (J A' : E) : ℝ :=
  - inner ℝ (T (D₃ A')) J
  - inner ℝ A' (Δπ (T (D A')))
  + (1 / 2 : ℝ) *
      (inner ℝ (T (D A')) (Δπ (P (D A'))) +
       inner ℝ (P (D A')) (Δπ (T (D A'))) +
       inner ℝ (T (D A')) (Δπ (T (D A'))))
  + (V₀ (A' - (P (D A') + T (D A'))) -
      V₀ (A' - P (D A')))

/-- One exact ordered increment.  This is a purely algebraic identity and
does not require differentiability or a convergence hypothesis. -/
theorem cmp102Eq80GlobalPotential_add_minimizer
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D D₃ : E → F) (V₀ : E → ℝ)
    (P T : F →L[ℝ] E) (Δπ : E →L[ℝ] E)
    (J A' : E) :
    cmp102Eq80GlobalPotential D D₃ V₀ (P + T) Δπ J A' =
      cmp102Eq80GlobalPotential D D₃ V₀ P Δπ J A' +
        cmp102Eq80MinimizerIncrement D D₃ V₀ P T Δπ J A' := by
  simp only [cmp102Eq80GlobalPotential,
    cmp102Eq80MinimizerIncrement,
    ContinuousLinearMap.add_apply, map_add,
    inner_add_left, inner_add_right]
  ring

/-- The exact one-step increment is the FTC integral of the literal
propagator-directional derivative along `P + t T`.  This exposes the
anchor/walk interaction before any connected-domain grouping. -/
theorem cmp102Eq80MinimizerIncrement_eq_integral_directionalDerivative
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D D₃ : E → F) (V₀ : E → ℝ)
    (P T : F →L[ℝ] E) (Δπ : E →L[ℝ] E)
    (J A' : E) (hV₀ : ContDiff ℝ 1 V₀) :
    cmp102Eq80MinimizerIncrement D D₃ V₀ P T Δπ J A' =
      ∫ t in (0 : ℝ)..1,
        cmp102Eq80PropagatorDirectionalDerivative D D₃
          (P + t • T) T Δπ J A'
          (fderiv ℝ V₀ (A' - (P + t • T) (D A'))) := by
  let curve := fun t : ℝ =>
    cmp102Eq80GlobalPotential D D₃ V₀ (P + t • T) Δπ J A'
  let derivative := fun t : ℝ =>
    cmp102Eq80PropagatorDirectionalDerivative D D₃
      (P + t • T) T Δπ J A'
      (fderiv ℝ V₀ (A' - (P + t • T) (D A')))
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt curve (derivative t) t := by
    intro t _ht
    exact
      hasDerivAt_cmp102Eq80GlobalPotential_affinePropagator
        D D₃ V₀ P T Δπ J A' t
        (fderiv ℝ V₀ (A' - (P + t • T) (D A')))
        ((hV₀.differentiable one_ne_zero
          (A' - (P + t • T) (D A'))).hasFDerivAt)
  have hHcurve : Continuous fun t : ℝ => P + t • T := by
    fun_prop
  have hderivative : Continuous derivative := by
    exact
      continuous_cmp102Eq80PropagatorDirectionalDerivative
        D D₃ V₀ (fun t : ℝ => P + t • T) T Δπ J A'
        hHcurve (hV₀.continuous_fderiv one_ne_zero)
  have hint : IntervalIntegrable derivative volume 0 1 :=
    hderivative.continuousOn.intervalIntegrable
  have hftc :
      (∫ t in (0 : ℝ)..1, derivative t) =
        curve 1 - curve 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [show
    (∫ t in (0 : ℝ)..1,
      cmp102Eq80PropagatorDirectionalDerivative D D₃
        (P + t • T) T Δπ J A'
        (fderiv ℝ V₀ (A' - (P + t • T) (D A')))) =
      curve 1 - curve 0 by exact hftc]
  have hadd :=
    cmp102Eq80GlobalPotential_add_minimizer
      D D₃ V₀ P T Δπ J A'
  dsimp [curve]
  simp only [one_smul, zero_smul, add_zero]
  linarith

/-- Ordered prefix of a minimizer series. -/
noncomputable def cmp102Eq80MinimizerPartialSum
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (term : ℕ → (F →L[ℝ] E)) (n : ℕ) : F →L[ℝ] E :=
  ∑ i ∈ Finset.range n, term i

@[simp]
theorem cmp102Eq80MinimizerPartialSum_zero
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (term : ℕ → (F →L[ℝ] E)) :
    cmp102Eq80MinimizerPartialSum term 0 = 0 := by
  simp [cmp102Eq80MinimizerPartialSum]

theorem cmp102Eq80MinimizerPartialSum_succ
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (term : ℕ → (F →L[ℝ] E)) (n : ℕ) :
    cmp102Eq80MinimizerPartialSum term (n + 1) =
      cmp102Eq80MinimizerPartialSum term n + term n := by
  simp [cmp102Eq80MinimizerPartialSum, Finset.sum_range_succ]

/-- Exact finite ordered telescoping of the nonlinear equation-(80)
potential along minimizer partial sums. -/
theorem cmp102Eq80GlobalPotential_partialSum_eq_sum_increments
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D D₃ : E → F) (V₀ : E → ℝ)
    (term : ℕ → (F →L[ℝ] E))
    (Δπ : E →L[ℝ] E) (J A' : E) :
    ∀ n : ℕ,
      cmp102Eq80GlobalPotential D D₃ V₀
          (cmp102Eq80MinimizerPartialSum term n) Δπ J A' =
        cmp102Eq80GlobalPotential D D₃ V₀ 0 Δπ J A' +
          ∑ i ∈ Finset.range n,
            cmp102Eq80MinimizerIncrement D D₃ V₀
              (cmp102Eq80MinimizerPartialSum term i) (term i)
              Δπ J A' := by
  intro n
  induction n with
  | zero =>
      simp [cmp102Eq80MinimizerPartialSum]
  | succ n ih =>
      rw [cmp102Eq80MinimizerPartialSum_succ,
        cmp102Eq80GlobalPotential_add_minimizer, ih,
        Finset.sum_range_succ]
      ring

/-- For a fixed physical field, equation (80) is continuous as a function
of the rectangular minimizer. -/
theorem continuous_cmp102Eq80GlobalPotential_minimizer
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D D₃ : E → F) (V₀ : E → ℝ)
    (Δπ : E →L[ℝ] E) (J A' : E)
    (hV₀ : Continuous V₀) :
    Continuous fun H : F →L[ℝ] E =>
      cmp102Eq80GlobalPotential D D₃ V₀ H Δπ J A' := by
  let evalD : (F →L[ℝ] E) →L[ℝ] E :=
    (ContinuousLinearMap.apply ℝ E) (D A')
  let evalD₃ : (F →L[ℝ] E) →L[ℝ] E :=
    (ContinuousLinearMap.apply ℝ E) (D₃ A')
  have hHD : Continuous fun H : F →L[ℝ] E => H (D A') := by
    simpa [evalD] using evalD.continuous
  have hHD₃ : Continuous fun H : F →L[ℝ] E => H (D₃ A') := by
    simpa [evalD₃] using evalD₃.continuous
  have hΔHD : Continuous fun H : F →L[ℝ] E =>
      Δπ (H (D A')) :=
    Δπ.continuous.comp hHD
  have hfirst : Continuous fun H : F →L[ℝ] E =>
      -inner ℝ (H (D₃ A')) J :=
    (hHD₃.inner continuous_const).neg
  have hsecond : Continuous fun H : F →L[ℝ] E =>
      -inner ℝ A' (Δπ (H (D A'))) :=
    (continuous_const.inner hΔHD).neg
  have hthird : Continuous fun H : F →L[ℝ] E =>
      (1 / 2 : ℝ) *
        inner ℝ (H (D A')) (Δπ (H (D A'))) :=
    continuous_const.mul (hHD.inner hΔHD)
  have hfourth : Continuous fun H : F →L[ℝ] E =>
      V₀ (A' - H (D A')) :=
    hV₀.comp (continuous_const.sub hHD)
  simpa [cmp102Eq80GlobalPotential] using
    ((hfirst.add hsecond).add hthird).add hfourth

/-- Passing from the finite telescoping identity to the complete minimizer
uses only the original ordered partial sums and continuity of `V₀`.
The conclusion is deliberately a `Tendsto`, not a rearrangeable `HasSum`
claim for the nonlinear increments. -/
theorem
    tendsto_cmp102Eq80GlobalPotential_partialSum_increments
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D D₃ : E → F) (V₀ : E → ℝ)
    (term : ℕ → (F →L[ℝ] E))
    (Δπ : E →L[ℝ] E) (J A' : E)
    (hV₀ : Continuous V₀) (hterm : Summable term) :
    Filter.Tendsto
      (fun n =>
        ∑ i ∈ Finset.range n,
          cmp102Eq80MinimizerIncrement D D₃ V₀
            (cmp102Eq80MinimizerPartialSum term i) (term i)
            Δπ J A')
      Filter.atTop
      (nhds
        (cmp102Eq80GlobalPotential D D₃ V₀ (∑' i, term i) Δπ J A' -
          cmp102Eq80GlobalPotential D D₃ V₀ 0 Δπ J A')) := by
  have hpartial :
      Filter.Tendsto
        (cmp102Eq80MinimizerPartialSum term)
        Filter.atTop (nhds (∑' i, term i)) := by
    simpa [cmp102Eq80MinimizerPartialSum] using
      hterm.hasSum.tendsto_sum_nat
  have hpotential :
      Filter.Tendsto
        (fun n =>
          cmp102Eq80GlobalPotential D D₃ V₀
            (cmp102Eq80MinimizerPartialSum term n) Δπ J A')
        Filter.atTop
        (nhds
          (cmp102Eq80GlobalPotential D D₃ V₀
            (∑' i, term i) Δπ J A')) :=
    (continuous_cmp102Eq80GlobalPotential_minimizer
      D D₃ V₀ Δπ J A' hV₀).continuousAt.tendsto.comp hpartial
  have hdiff := hpotential.sub
    (tendsto_const_nhds :
      Filter.Tendsto
        (fun _ : ℕ =>
          cmp102Eq80GlobalPotential D D₃ V₀ 0 Δπ J A')
        Filter.atTop
        (nhds (cmp102Eq80GlobalPotential D D₃ V₀ 0 Δπ J A')))
  convert hdiff using 1
  funext n
  rw [cmp102Eq80GlobalPotential_partialSum_eq_sum_increments]
  ring

end

end YangMills.RG
