/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214CauchyEstimate

/-!
# CMP116 equation (2.14): norm bounds for the full Gaussian integrand

This module removes the cutoff and probability-integration bookkeeping from
the open contour estimate.  The literal small- and large-field factors have
norm at most one.  Hence a pointwise bound on the Wilson/Gaussian weights and
the real part of the interaction exponent propagates through both probability
integrals in equation (2.14).

The remaining hypotheses are now the genuinely physical ones: bounds for the
outer quadratic weight, the inner bilinear weight, and the interaction
potential.  No Wilson-Hessian estimate is asserted here.
-/

namespace YangMills.RG

open MeasureTheory
open scoped BigOperators

/-- A literal small-field indicator has complex norm at most one. -/
theorem norm_cmp116SmallFieldIndicator_le_one
    {E : Type*} [Norm E] (threshold : ℝ) (x : E) :
    ‖cmp116SmallFieldIndicator threshold x‖ ≤ 1 := by
  by_cases h : ‖x‖ < threshold <;>
    simp [cmp116SmallFieldIndicator, h]

/-- A literal large-field indicator has complex norm at most one. -/
theorem norm_cmp116LargeFieldIndicator_le_one
    {E : Type*} [Norm E] (threshold : ℝ) (x : E) :
    ‖cmp116LargeFieldIndicator threshold x‖ ≤ 1 := by
  by_cases h : threshold ≤ ‖x‖ <;>
    simp [cmp116LargeFieldIndicator, h]

/-- Products of small-field indicators remain contractions. -/
theorem norm_cmp116SmallFieldCutoff_le_one
    {β E : Type*} [Norm E] (carrier : Finset β)
    (threshold : ℝ) (B : β → E) :
    ‖cmp116SmallFieldCutoff carrier threshold B‖ ≤ 1 := by
  classical
  unfold cmp116SmallFieldCutoff
  rw [norm_prod]
  apply Finset.prod_le_one
  · intro b hb
    exact norm_nonneg _
  · intro b hb
    exact norm_cmp116SmallFieldIndicator_le_one threshold (B b)

/-- Products of large-field indicators remain contractions. -/
theorem norm_cmp116LargeFieldCutoff_le_one
    {β E : Type*} [Norm E] (P : Finset β)
    (threshold : ℝ) (B : β → E) :
    ‖cmp116LargeFieldCutoff P threshold B‖ ≤ 1 := by
  classical
  unfold cmp116LargeFieldCutoff
  rw [norm_prod]
  apply Finset.prod_le_one
  · intro b hb
    exact norm_nonneg _
  · intro b hb
    exact norm_cmp116LargeFieldIndicator_le_one threshold (B b)

/-- The complete signed cutoff factor in (2.14) has norm at most one. -/
theorem CMP116Eq214AnalyticData.norm_cutoffFactor_le_one
    {nDelta nY : ℕ} {Bond X B Ψ Φ E : Type*}
    [MeasurableSpace X] [MeasurableSpace B] [Norm E]
    (A : CMP116Eq214AnalyticData nDelta nY Bond X B Ψ Φ E)
    (Y0 P : Finset Bond) (b : B) :
    ‖A.cutoffFactor Y0 P b‖ ≤ 1 := by
  classical
  rw [CMP116Eq214AnalyticData.cutoffFactor, norm_mul, norm_mul]
  have hsign : ‖(-1 : ℂ) ^ P.card‖ = 1 := by simp
  rw [hsign, one_mul]
  calc
    ‖cmp116SmallFieldCutoff Y0 A.threshold (A.bondField b)‖ *
        ‖cmp116LargeFieldCutoff P A.threshold (A.bondField b)‖ ≤
      1 * 1 := mul_le_mul
        (norm_cmp116SmallFieldCutoff_le_one Y0 A.threshold (A.bondField b))
        (norm_cmp116LargeFieldCutoff_le_one P A.threshold (A.bondField b))
        (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- Pointwise reduction of the inner integrand to the physical weight and the
real part of its interaction exponent. -/
theorem CMP116Eq214AnalyticData.norm_innerIntegrand_le
    {nDelta nY : ℕ} {Bond X B Ψ Φ E : Type*}
    [MeasurableSpace X] [MeasurableSpace B] [Norm E]
    (A : CMP116Eq214AnalyticData nDelta nY Bond X B Ψ Φ E)
    (Y0 P : Finset Bond)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : Ψ) (phi : Φ) (x : X) (b : B)
    (innerBound interactionBound : ℝ)
    (hinner : ‖A.innerWeight sigma tau psi phi x b‖ ≤ innerBound)
    (hinteraction :
      (A.interactionExponent sigma tau psi phi b).re ≤ interactionBound) :
    ‖A.innerIntegrand Y0 P sigma tau psi phi x b‖ ≤
      innerBound * Real.exp interactionBound := by
  rw [CMP116Eq214AnalyticData.innerIntegrand, norm_mul, norm_mul,
    Complex.norm_exp]
  have hinner_nonneg : 0 ≤ innerBound :=
    (norm_nonneg (A.innerWeight sigma tau psi phi x b)).trans hinner
  calc
    ‖A.innerWeight sigma tau psi phi x b‖ * ‖A.cutoffFactor Y0 P b‖ *
        Real.exp (A.interactionExponent sigma tau psi phi b).re ≤
      innerBound * ‖A.cutoffFactor Y0 P b‖ *
        Real.exp (A.interactionExponent sigma tau psi phi b).re := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hinner (norm_nonneg _))
            (Real.exp_pos _).le
    _ ≤ innerBound * 1 *
        Real.exp (A.interactionExponent sigma tau psi phi b).re := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (A.norm_cutoffFactor_le_one Y0 P b) hinner_nonneg)
            (Real.exp_pos _).le
    _ ≤ innerBound * 1 * Real.exp interactionBound := by
          exact mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr hinteraction)
            (mul_nonneg hinner_nonneg zero_le_one)
    _ = innerBound * Real.exp interactionBound := by ring

/-- Probability integration propagates uniform physical bounds through the
complete nested Gaussian integral at fixed contour parameters. -/
theorem CMP116Eq214AnalyticData.norm_analyticIntegrand_le
    {nDelta nY : ℕ} {Bond X B Ψ Φ E : Type*}
    [MeasurableSpace X] [MeasurableSpace B] [Norm E]
    (A : CMP116Eq214AnalyticData nDelta nY Bond X B Ψ Φ E)
    (Y0 P : Finset Bond)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : Ψ) (phi : Φ)
    (outerBound innerBound interactionBound : ℝ)
    (houter_nonneg : 0 ≤ outerBound)
    (hmu0 : IsProbabilityMeasure A.mu0)
    (hmuB : IsProbabilityMeasure (A.conditionedMeasure sigma tau))
    (houter : ∀ x,
      ‖A.outerWeight sigma tau psi phi x‖ ≤ outerBound)
    (hinner : ∀ x b,
      ‖A.innerWeight sigma tau psi phi x b‖ ≤ innerBound)
    (hinteraction : ∀ b,
      (A.interactionExponent sigma tau psi phi b).re ≤ interactionBound) :
    ‖A.analyticIntegrand Y0 P sigma tau psi phi‖ ≤
      outerBound * (innerBound * Real.exp interactionBound) := by
  letI : IsProbabilityMeasure A.mu0 := hmu0
  have hinnerIntegral (x : X) :
      ‖∫ b, A.innerIntegrand Y0 P sigma tau psi phi x b
          ∂A.conditionedMeasure sigma tau‖ ≤
        innerBound * Real.exp interactionBound := by
    letI : IsProbabilityMeasure (A.conditionedMeasure sigma tau) := hmuB
    simpa using
      (MeasureTheory.norm_integral_le_of_norm_le_const
        (μ := A.conditionedMeasure sigma tau)
        (Filter.Eventually.of_forall fun b =>
          A.norm_innerIntegrand_le Y0 P sigma tau psi phi x b
            innerBound interactionBound (hinner x b) (hinteraction b)))
  unfold CMP116Eq214AnalyticData.analyticIntegrand
  simpa using
    (MeasureTheory.norm_integral_le_of_norm_le_const
      (μ := A.mu0)
      (Filter.Eventually.of_forall fun x => by
        rw [norm_mul]
        exact mul_le_mul (houter x) (hinnerIntegral x)
          (norm_nonneg _)
          houter_nonneg))

/-- A uniform bound on a finite Cauchy family implies the recursive contour
predicate used by the quantitative Cauchy theorem. -/
theorem cmp116Eq214CauchyBoundaryBound_of_forall_norm_le
    (n : ℕ) (radius : Fin n → ℝ)
    (F : (Fin n → ℂ) → ℂ) (M : ℝ)
    (hF : ∀ z, ‖F z‖ ≤ M) :
    CMP116Eq214CauchyBoundaryBound n radius F M := by
  induction n with
  | zero =>
      simpa [CMP116Eq214CauchyBoundaryBound] using hF Fin.elim0
  | succ n ih =>
      simp only [CMP116Eq214CauchyBoundaryBound]
      intro s hs z hz
      apply ih
      intro tail
      exact hF (Fin.cons z tail)

/-- The analogous uniform-to-boundary conversion for the two nested Cauchy
families of equation (2.14). -/
theorem cmp116Eq214NestedCauchyBoundaryBound_of_forall_norm_le
    (nDelta nY : ℕ)
    (deltaRadius : Fin nDelta → ℝ) (yRadius : Fin nY → ℝ)
    (F : (Fin nDelta → ℂ) → (Fin nY → ℂ) → ℂ) (M : ℝ)
    (hF : ∀ sigma tau, ‖F sigma tau‖ ≤ M) :
    CMP116Eq214NestedCauchyBoundaryBound nDelta nY
      deltaRadius yRadius F M := by
  induction nDelta with
  | zero =>
      simpa [CMP116Eq214NestedCauchyBoundaryBound] using
        cmp116Eq214CauchyBoundaryBound_of_forall_norm_le
          nY yRadius (F Fin.elim0) M (hF Fin.elim0)
  | succ nDelta ih =>
      simp only [CMP116Eq214NestedCauchyBoundaryBound]
      intro s hs z hz
      apply ih
      intro sigmaTail tau
      exact hF (Fin.cons z sigmaTail) tau

/-- Uniform physical weight estimates generate the complete `hcontour`
obligation consumed by the canonical Cauchy majorant.  Cutoffs and both
probability integrations have disappeared from the hypotheses. -/
theorem CMP116Eq214AnalyticData.nestedCauchyBoundaryBound_of_uniformPhysicalBounds
    {nDelta nY : ℕ} {Bond X B Ψ Φ E : Type*}
    [MeasurableSpace X] [MeasurableSpace B] [Norm E]
    (A : CMP116Eq214AnalyticData nDelta nY Bond X B Ψ Φ E)
    (Y0 P : Finset Bond) (psi : Ψ) (phi : Φ)
    (outerBound innerBound interactionBound : ℝ)
    (houter_nonneg : 0 ≤ outerBound)
    (hmu0 : IsProbabilityMeasure A.mu0)
    (hmuB : ∀ sigma tau,
      IsProbabilityMeasure (A.conditionedMeasure sigma tau))
    (houter : ∀ sigma tau x,
      ‖A.outerWeight sigma tau psi phi x‖ ≤ outerBound)
    (hinner : ∀ sigma tau x b,
      ‖A.innerWeight sigma tau psi phi x b‖ ≤ innerBound)
    (hinteraction : ∀ sigma tau b,
      (A.interactionExponent sigma tau psi phi b).re ≤ interactionBound) :
    CMP116Eq214NestedCauchyBoundaryBound nDelta nY
      A.deltaRadius A.yRadius
      (fun sigma tau => A.analyticIntegrand Y0 P sigma tau psi phi)
      (outerBound * (innerBound * Real.exp interactionBound)) := by
  apply cmp116Eq214NestedCauchyBoundaryBound_of_forall_norm_le
  intro sigma tau
  exact A.norm_analyticIntegrand_le Y0 P sigma tau psi phi
    outerBound innerBound interactionBound houter_nonneg hmu0
    (hmuB sigma tau) (houter sigma tau) (hinner sigma tau)
    (hinteraction sigma tau)

end YangMills.RG
