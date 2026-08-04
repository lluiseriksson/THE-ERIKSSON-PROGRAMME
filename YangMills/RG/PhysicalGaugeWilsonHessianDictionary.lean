/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalGaugeCMP116Dictionary

/-!
# Wilson Hessian / Green inverse source dictionary

This module names the single-scale source-to-Lean dictionary that should sit
behind the currently opaque `wilson_hessian_identification` field.

Honest scope: the dictionary is not a covariance-root theorem, a Gaussian
pushforward theorem, a local-activity construction theorem, or an `hraw`
estimate.  It records the exact contract needed to identify the CMP102
positive Hessian operator and the CMP99 background-field Green operator with
the repository precision/covariance pair after a declared gauge-slice
coordinate transport and an explicit normalization scalar.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

/-- Source-to-Lean dictionary for the Wilson Hessian / Green inverse at one
scale.

The type `V` is the already gauge-fixed source slice/domain.  Therefore the
inverse identities are stated against `ContinuousLinearMap.id ℝ V`; if a source
theorem later only supplies inverse identities modulo a projector, that should
be represented by a separate projector-valued dictionary rather than silently
strengthening the source statement.
-/
structure PhysicalGaugeWilsonHessianSourceDictionary
    {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]
    (D :
      PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (toPhysical :
      V ≃L[ℝ] PhysicalGaugeOneCochain dPhys N Nc)
    (precision covariance :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc)
    (sourceHessian sourceGreen : V →L[ℝ] V)
    (sourceQuadratic : V → V → ℝ)
    (hessianScale : ℝ)
    (cmp102Expansion : Prop)
    (cmp99GreenIdentification : Prop) : Prop where
  /-- Positive normalization carrying sign, `1/2`, volume, coupling, block
  scale, and source/repository inner-product conventions. -/
  scale_pos :
    0 < hessianScale
  /-- CMP102 Eq. (142)-style expansion/positivity package, kept as source
  content rather than proved from notation here. -/
  cmp102_expansion :
    cmp102Expansion
  /-- The source quadratic form is represented by the declared source Hessian. -/
  source_quadratic_represents_hessian :
    ∀ a b, sourceQuadratic a b = inner ℝ a (sourceHessian b)
  /-- Positivity of the source Hessian quadratic form on the gauge slice. -/
  source_hessian_positive :
    ∀ a, 0 ≤ sourceQuadratic a a
  /-- CMP99 `G(U_k)` has been identified with `sourceGreen` on the same source
  gauge slice/domain. -/
  cmp99_green_identification :
    cmp99GreenIdentification
  /-- `sourceGreen` is a left inverse of the source Hessian on `V`. -/
  source_green_left_inverse :
    sourceGreen.comp sourceHessian = ContinuousLinearMap.id ℝ V
  /-- `sourceGreen` is a right inverse of the source Hessian on `V`. -/
  source_green_right_inverse :
    sourceHessian.comp sourceGreen = ContinuousLinearMap.id ℝ V
  /-- Bilinear sign and inner-product normalization dictionary from the source
  Hessian form to the repository precision form. -/
  precision_quadratic_transport :
    ∀ a b,
      inner ℝ (toPhysical a) (precision (toPhysical b)) =
        hessianScale * sourceQuadratic a b
  /-- The repository covariance is the transported inverse Hessian, not a
  covariance-root or Gaussian-pushforward statement. -/
  covariance_transport :
    covariance =
      toPhysical.toContinuousLinearMap.comp
        (((hessianScale)⁻¹ • sourceGreen).comp
          toPhysical.symm.toContinuousLinearMap)

namespace PhysicalGaugeWilsonHessianSourceDictionary

variable
    {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]
    {D :
      PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim}
    {toPhysical :
      V ≃L[ℝ] PhysicalGaugeOneCochain dPhys N Nc}
    {precision covariance :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc}
    {sourceHessian sourceGreen : V →L[ℝ] V}
    {sourceQuadratic : V → V → ℝ}
    {hessianScale : ℝ}
    {cmp102Expansion cmp99GreenIdentification : Prop}

/-- Thin constructor for the Wilson Hessian / Green inverse source dictionary.

All analytic and source-identification content remains explicit in the fields;
the theorem only packages the source-facing contract. -/
theorem of_components
    (scale_pos : 0 < hessianScale)
    (cmp102_expansion : cmp102Expansion)
    (source_quadratic_represents_hessian :
      ∀ a b, sourceQuadratic a b = inner ℝ a (sourceHessian b))
    (source_hessian_positive :
      ∀ a, 0 ≤ sourceQuadratic a a)
    (cmp99_green_identification : cmp99GreenIdentification)
    (source_green_left_inverse :
      sourceGreen.comp sourceHessian = ContinuousLinearMap.id ℝ V)
    (source_green_right_inverse :
      sourceHessian.comp sourceGreen = ContinuousLinearMap.id ℝ V)
    (precision_quadratic_transport :
      ∀ a b,
        inner ℝ (toPhysical a) (precision (toPhysical b)) =
          hessianScale * sourceQuadratic a b)
    (covariance_transport :
      covariance =
        toPhysical.toContinuousLinearMap.comp
          (((hessianScale)⁻¹ • sourceGreen).comp
            toPhysical.symm.toContinuousLinearMap)) :
    PhysicalGaugeWilsonHessianSourceDictionary
      D toPhysical precision covariance sourceHessian sourceGreen
      sourceQuadratic hessianScale cmp102Expansion
      cmp99GreenIdentification where
  scale_pos := scale_pos
  cmp102_expansion := cmp102_expansion
  source_quadratic_represents_hessian :=
    source_quadratic_represents_hessian
  source_hessian_positive := source_hessian_positive
  cmp99_green_identification := cmp99_green_identification
  source_green_left_inverse := source_green_left_inverse
  source_green_right_inverse := source_green_right_inverse
  precision_quadratic_transport := precision_quadratic_transport
  covariance_transport := covariance_transport

/-- Projection of the transported covariance identity. -/
theorem covariance_eq_transport
    (h :
      PhysicalGaugeWilsonHessianSourceDictionary
        D toPhysical precision covariance sourceHessian sourceGreen
        sourceQuadratic hessianScale cmp102Expansion
        cmp99GreenIdentification) :
    covariance =
      toPhysical.toContinuousLinearMap.comp
        (((hessianScale)⁻¹ • sourceGreen).comp
          toPhysical.symm.toContinuousLinearMap) :=
  h.covariance_transport

/-- Projection of the transported precision quadratic-form identity. -/
theorem precision_quadratic_transport_apply
    (h :
      PhysicalGaugeWilsonHessianSourceDictionary
        D toPhysical precision covariance sourceHessian sourceGreen
        sourceQuadratic hessianScale cmp102Expansion
        cmp99GreenIdentification)
    (a b : V) :
    inner ℝ (toPhysical a) (precision (toPhysical b)) =
      hessianScale * sourceQuadratic a b :=
  h.precision_quadratic_transport a b

end PhysicalGaugeWilsonHessianSourceDictionary

/-- Single-scale alias for using a Wilson Hessian / Green source dictionary as
the currently opaque `wilsonHessianIdentification` proposition. -/
abbrev physicalGaugeWilsonHessianIdentification
    {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]
    (D :
      PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (toPhysical :
      V ≃L[ℝ] PhysicalGaugeOneCochain dPhys N Nc)
    (precision covariance :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc)
    (sourceHessian sourceGreen : V →L[ℝ] V)
    (sourceQuadratic : V → V → ℝ)
    (hessianScale : ℝ)
    (cmp102Expansion cmp99GreenIdentification : Prop) : Prop :=
  PhysicalGaugeWilsonHessianSourceDictionary
    D toPhysical precision covariance sourceHessian sourceGreen
    sourceQuadratic hessianScale cmp102Expansion cmp99GreenIdentification

end YangMills.RG
