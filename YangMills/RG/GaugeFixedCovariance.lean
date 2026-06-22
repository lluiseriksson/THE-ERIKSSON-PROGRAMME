/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.CoerciveCovariance
import YangMills.RG.GaugeFixedPrecision

/-!
# Exact covariance for the abstract gauge-fixed precision form

This module composes two already-verified P4 deterministic layers:

* `GaugeFixedPrecision`: a block-Poincare/Hodge estimate plus a summable
  operator-norm budget gives strict coercivity for
  `K0 + a Q†Q - ∑' i, Sigma i`;
* `CoerciveCovariance`: strict finite-dimensional coercivity gives the exact
  inverse covariance, inverse identities, norm bound, and PSD quadratic form.

The result is still abstract Hilbert-space algebra.  It does not identify
`K0`, `Q`, or `Sigma` with the physical Yang--Mills Hessian, block derivative,
or self-energy.  It is a named assembly point for the future theorem
`physicalGaugeFixedPrecision_coercive`, once the source-level Hodge/Poincare
and background perturbation estimates have been proved.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

open scoped BigOperators RealInnerProductSpace

/-- The residual coercivity constant for the abstract gauge-fixed precision
form. -/
noncomputable def gaugeFixedResidualCoercivityConstant
    {ι : Type*} (δ : ι → ℝ) (a CP : ℝ) : ℝ :=
  min 1 a / CP - ∑' i, δ i

/-- The exact covariance of the abstract gauge-fixed precision operator,
constructed from block-Poincare/Hodge and perturbation-budget hypotheses.

This is intentionally not a physical Yang--Mills theorem: the physical
identification of `K0`, `Q`, and `Sigma` remains a separate source obligation. -/
noncomputable def covarianceOfGaugeFixedPrecisionCLM
    {ι E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (K0 : E →L[ℝ] E)
    (Q : E →L[ℝ] F)
    (Sigma : ι → E →L[ℝ] E)
    (δ : ι → ℝ)
    {a CP : ℝ}
    (ha : 0 < a)
    (hCP : 0 < CP)
    (hK0nonneg :
      ∀ x : E, 0 ≤ inner ℝ x (K0 x))
    (hPoincare :
      ∀ x : E,
        ‖x‖ ^ 2 ≤
          CP * (inner ℝ x (K0 x) + ‖Q x‖ ^ 2))
    (hδ : Summable δ)
    (hSigmaδ :
      ∀ i, ‖Sigma i‖ ≤ δ i)
    (hbudget :
      (∑' i, δ i) < min 1 a / CP) :
    E →L[ℝ] E :=
  let hcoer :=
    gaugeFixedPrecision_coerciveWithPositiveConstant
      K0 Q Sigma δ ha hCP hK0nonneg hPoincare hδ hSigmaδ hbudget
  covarianceOfIsCoerciveCLM
    (gaugeFixedPrecisionCLM K0 Q a Sigma)
    hcoer.1
    hcoer.2

/-- Left-inverse identity for the covariance of the abstract gauge-fixed
precision form. -/
theorem covarianceOfGaugeFixedPrecisionCLM_comp_precision
    {ι E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (K0 : E →L[ℝ] E)
    (Q : E →L[ℝ] F)
    (Sigma : ι → E →L[ℝ] E)
    (δ : ι → ℝ)
    {a CP : ℝ}
    (ha : 0 < a)
    (hCP : 0 < CP)
    (hK0nonneg :
      ∀ x : E, 0 ≤ inner ℝ x (K0 x))
    (hPoincare :
      ∀ x : E,
        ‖x‖ ^ 2 ≤
          CP * (inner ℝ x (K0 x) + ‖Q x‖ ^ 2))
    (hδ : Summable δ)
    (hSigmaδ :
      ∀ i, ‖Sigma i‖ ≤ δ i)
    (hbudget :
      (∑' i, δ i) < min 1 a / CP) :
    (covarianceOfGaugeFixedPrecisionCLM
        K0 Q Sigma δ ha hCP hK0nonneg hPoincare hδ hSigmaδ hbudget).comp
      (gaugeFixedPrecisionCLM K0 Q a Sigma) =
        ContinuousLinearMap.id ℝ E := by
  dsimp [covarianceOfGaugeFixedPrecisionCLM]
  exact
    covarianceOfIsCoerciveCLM_comp_precision
      (gaugeFixedPrecisionCLM K0 Q a Sigma)
      (gaugeFixedPrecision_coerciveWithPositiveConstant
        K0 Q Sigma δ ha hCP hK0nonneg hPoincare hδ hSigmaδ hbudget).1
      (gaugeFixedPrecision_coerciveWithPositiveConstant
        K0 Q Sigma δ ha hCP hK0nonneg hPoincare hδ hSigmaδ hbudget).2

/-- Right-inverse identity for the covariance of the abstract gauge-fixed
precision form. -/
theorem precision_comp_covarianceOfGaugeFixedPrecisionCLM
    {ι E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (K0 : E →L[ℝ] E)
    (Q : E →L[ℝ] F)
    (Sigma : ι → E →L[ℝ] E)
    (δ : ι → ℝ)
    {a CP : ℝ}
    (ha : 0 < a)
    (hCP : 0 < CP)
    (hK0nonneg :
      ∀ x : E, 0 ≤ inner ℝ x (K0 x))
    (hPoincare :
      ∀ x : E,
        ‖x‖ ^ 2 ≤
          CP * (inner ℝ x (K0 x) + ‖Q x‖ ^ 2))
    (hδ : Summable δ)
    (hSigmaδ :
      ∀ i, ‖Sigma i‖ ≤ δ i)
    (hbudget :
      (∑' i, δ i) < min 1 a / CP) :
    (gaugeFixedPrecisionCLM K0 Q a Sigma).comp
      (covarianceOfGaugeFixedPrecisionCLM
        K0 Q Sigma δ ha hCP hK0nonneg hPoincare hδ hSigmaδ hbudget) =
        ContinuousLinearMap.id ℝ E := by
  dsimp [covarianceOfGaugeFixedPrecisionCLM]
  exact
    precision_comp_covarianceOfIsCoerciveCLM
      (gaugeFixedPrecisionCLM K0 Q a Sigma)
      (gaugeFixedPrecision_coerciveWithPositiveConstant
        K0 Q Sigma δ ha hCP hK0nonneg hPoincare hδ hSigmaδ hbudget).1
      (gaugeFixedPrecision_coerciveWithPositiveConstant
        K0 Q Sigma δ ha hCP hK0nonneg hPoincare hδ hSigmaδ hbudget).2

/-- Operator-norm bound for the covariance of the abstract gauge-fixed
precision form. -/
theorem norm_covarianceOfGaugeFixedPrecisionCLM_le
    {ι E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (K0 : E →L[ℝ] E)
    (Q : E →L[ℝ] F)
    (Sigma : ι → E →L[ℝ] E)
    (δ : ι → ℝ)
    {a CP : ℝ}
    (ha : 0 < a)
    (hCP : 0 < CP)
    (hK0nonneg :
      ∀ x : E, 0 ≤ inner ℝ x (K0 x))
    (hPoincare :
      ∀ x : E,
        ‖x‖ ^ 2 ≤
          CP * (inner ℝ x (K0 x) + ‖Q x‖ ^ 2))
    (hδ : Summable δ)
    (hSigmaδ :
      ∀ i, ‖Sigma i‖ ≤ δ i)
    (hbudget :
      (∑' i, δ i) < min 1 a / CP) :
    ‖covarianceOfGaugeFixedPrecisionCLM
        K0 Q Sigma δ ha hCP hK0nonneg hPoincare hδ hSigmaδ hbudget‖ ≤
      (gaugeFixedResidualCoercivityConstant δ a CP)⁻¹ := by
  dsimp [covarianceOfGaugeFixedPrecisionCLM,
    gaugeFixedResidualCoercivityConstant]
  exact
    norm_covarianceOfIsCoerciveCLM_le
      (gaugeFixedPrecisionCLM K0 Q a Sigma)
      (gaugeFixedPrecision_coerciveWithPositiveConstant
        K0 Q Sigma δ ha hCP hK0nonneg hPoincare hδ hSigmaδ hbudget).1
      (gaugeFixedPrecision_coerciveWithPositiveConstant
        K0 Q Sigma δ ha hCP hK0nonneg hPoincare hδ hSigmaδ hbudget).2

/-- Positive-semidefinite covariance quadratic form for the abstract
gauge-fixed precision form. -/
theorem covarianceOfGaugeFixedPrecisionCLM_psd
    {ι E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (K0 : E →L[ℝ] E)
    (Q : E →L[ℝ] F)
    (Sigma : ι → E →L[ℝ] E)
    (δ : ι → ℝ)
    {a CP : ℝ}
    (ha : 0 < a)
    (hCP : 0 < CP)
    (hK0nonneg :
      ∀ x : E, 0 ≤ inner ℝ x (K0 x))
    (hPoincare :
      ∀ x : E,
        ‖x‖ ^ 2 ≤
          CP * (inner ℝ x (K0 x) + ‖Q x‖ ^ 2))
    (hδ : Summable δ)
    (hSigmaδ :
      ∀ i, ‖Sigma i‖ ≤ δ i)
    (hbudget :
      (∑' i, δ i) < min 1 a / CP)
    (y : E) :
    0 ≤
      inner ℝ y
        (covarianceOfGaugeFixedPrecisionCLM
          K0 Q Sigma δ ha hCP hK0nonneg hPoincare hδ hSigmaδ hbudget y) := by
  dsimp [covarianceOfGaugeFixedPrecisionCLM]
  exact
    covarianceOfIsCoerciveCLM_psd
      (gaugeFixedPrecisionCLM K0 Q a Sigma)
      (gaugeFixedPrecision_coerciveWithPositiveConstant
        K0 Q Sigma δ ha hCP hK0nonneg hPoincare hδ hSigmaδ hbudget).1
      (gaugeFixedPrecision_coerciveWithPositiveConstant
        K0 Q Sigma δ ha hCP hK0nonneg hPoincare hδ hSigmaδ hbudget).2
      y

end YangMills.RG
