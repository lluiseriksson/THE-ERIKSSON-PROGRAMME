import YangMills.RG.InverseSqrtResolventKernel
import YangMills.RG.InverseSqrtResolventScalar

/-!
# Bochner integrability of the inverse-square-root difference kernel

The pointwise second-resolvent factorization is now combined with:

* continuity of the chosen shifted resolvents on `(0,∞)`;
* the exact two-margin scalar kernel;
* its domination by the integrable common-margin majorant.

The terminal theorem proves that the operator-valued kernel is Bochner
integrable on `(0,∞)`.  This module deliberately stops before identifying
that integral with the difference of the canonical inverse square roots.
-/

namespace YangMills.RG

open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

/-- The norm of the operator kernel is dominated by the exact scalar
two-margin kernel times the physical precision defect. -/
theorem norm_inverseSqrtResolventDifferenceKernel_le_twoMargin
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K₀ K₁ : E →L[ℝ] E)
    {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hK₀ : IsCoerciveCLM K₀ c₀)
    (hK₁ : IsCoerciveCLM K₁ c₁)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖inverseSqrtResolventDifferenceKernel
        K₀ K₁ hc₀ hc₁ hK₀ hK₁ t‖ ≤
      ‖K₀ - K₁‖ * inverseSqrtTwoMarginScalar c₀ c₁ t := by
  have hbound :=
    norm_inverseSqrtResolventDifferenceKernel_le
      K₀ K₁ hc₀ hc₁ hK₀ hK₁ t ht
  unfold inverseSqrtTwoMarginScalar
  calc
    ‖inverseSqrtResolventDifferenceKernel
        K₀ K₁ hc₀ hc₁ hK₀ hK₁ t‖
        ≤ (Real.sqrt t)⁻¹ *
            ((c₁ + t)⁻¹ * ‖K₀ - K₁‖ * (c₀ + t)⁻¹) :=
      hbound
    _ = ‖K₀ - K₁‖ *
        ((Real.sqrt t)⁻¹ * (c₁ + t)⁻¹ * (c₀ + t)⁻¹) := by
      ring

/-- The inverse-square-root difference kernel is Bochner integrable on the
positive half-line. -/
theorem integrableOn_inverseSqrtResolventDifferenceKernel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K₀ K₁ : E →L[ℝ] E)
    {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hK₀ : IsCoerciveCLM K₀ c₀)
    (hK₁ : IsCoerciveCLM K₁ c₁) :
    IntegrableOn
      (inverseSqrtResolventDifferenceKernel
        K₀ K₁ hc₀ hc₁ hK₀ hK₁)
      (Ioi 0) := by
  have hscalar :=
    integrableOn_inverseSqrtTwoMarginScalar hc₀ hc₁
  have hmajorant :
      Integrable
        (fun t : ℝ =>
          ‖K₀ - K₁‖ * inverseSqrtTwoMarginScalar c₀ c₁ t)
        (volume.restrict (Ioi 0)) :=
    hscalar.const_mul ‖K₀ - K₁‖
  have hmeas :
      AEStronglyMeasurable
        (inverseSqrtResolventDifferenceKernel
          K₀ K₁ hc₀ hc₁ hK₀ hK₁)
        (volume.restrict (Ioi 0)) :=
    (continuousOn_inverseSqrtResolventDifferenceKernel
      K₀ K₁ hc₀ hc₁ hK₀ hK₁).aestronglyMeasurable
        measurableSet_Ioi
  refine Integrable.mono' hmajorant hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change 0 < t at ht
  exact norm_inverseSqrtResolventDifferenceKernel_le_twoMargin
    K₀ K₁ hc₀ hc₁ hK₀ hK₁ t ht.le

end

end YangMills.RG
