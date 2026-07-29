/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq222CutoffSuppression

/-!
# Interaction domination only on the physical cutoff support

The literal equation-(2.14) integrand contains the product of the small-field
and large-field cutoffs.  Consequently an interaction estimate is needed only
where that product is nonzero.  Requiring the estimate for every Gaussian
coordinate vector is strictly stronger and is not the source-faithful
interface for Balaban's small-field estimate (1.36).

This module proves the support-sensitive versions of the equation-(2.22) and
Gaussian-integration bounds.  It does not prove that the physical remainder
satisfies (1.36) on the cutoff support.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No placeholders or
local axioms.
-/

namespace YangMills.RG

open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

/-- A nonzero small-field product certifies the printed strict small-field
condition at every bond in its carrier. -/
theorem norm_lt_of_cmp116SmallFieldCutoff_ne_zero
    {β E : Type*} [DecidableEq β] [Norm E]
    (carrier : Finset β) (threshold : ℝ) (B : β → E)
    (hcutoff : cmp116SmallFieldCutoff carrier threshold B ≠ 0)
    {bond : β} (hbond : bond ∈ carrier) :
    ‖B bond‖ < threshold := by
  by_contra hsmall
  have hindicator :
      cmp116SmallFieldIndicator threshold (B bond) = 0 := by
    simp [cmp116SmallFieldIndicator, hsmall]
  apply hcutoff
  unfold cmp116SmallFieldCutoff
  exact Finset.prod_eq_zero hbond hindicator

/-- Nonvanishing of the complete signed cutoff implies the strict
small-field condition on every bond of `Y0`. -/
theorem CMP116Eq214AnalyticData.norm_bondField_lt_threshold_of_cutoffFactor_ne_zero
    {nDelta nY : ℕ} {Bond X B Ψ Φ E : Type*}
    [DecidableEq Bond] [MeasurableSpace X] [MeasurableSpace B] [Norm E]
    (G : CMP116Eq214AnalyticData nDelta nY Bond X B Ψ Φ E)
    (Y0 P : Finset Bond) (b : B)
    (hcutoff : G.cutoffFactor Y0 P b ≠ 0)
    {bond : Bond} (hbond : bond ∈ Y0) :
    ‖G.bondField b bond‖ < G.threshold := by
  have hsmall :
      cmp116SmallFieldCutoff Y0 G.threshold (G.bondField b) ≠ 0 := by
    intro hzero
    apply hcutoff
    simp [CMP116Eq214AnalyticData.cutoffFactor, hzero]
  exact norm_lt_of_cmp116SmallFieldCutoff_ne_zero
    Y0 G.threshold (G.bondField b) hsmall hbond

/-- The residual-cost inner-integrand bound only needs the interaction
estimate on the nonzero support of the literal cutoff factor. -/
theorem CMP116Eq214AnalyticData.norm_innerIntegrand_le_exp_residual_sub_cardPenalty_mul_realGaussian_of_cutoffSupport
    {nDelta nY : ℕ} {Bond X B Ψ Φ E ι : Type*}
    [MeasurableSpace X] [MeasurableSpace B] [Norm E] [Fintype ι]
    (G : CMP116Eq214AnalyticData nDelta nY Bond X B Ψ Φ E)
    (Y0 P : Finset Bond)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : Ψ) (phi : Φ) (x : X) (b : B)
    (u : ι → ℝ) (A : Matrix ι ι ℝ) (r : ι → ℝ)
    (gamma residual : ℝ)
    (hgamma : 0 ≤ gamma) (hthreshold : 0 ≤ G.threshold)
    (hinner :
      ‖G.innerWeight sigma tau psi phi x b‖ ≤
        Real.exp (∑ i, r i * u i))
    (hinteraction :
      G.cutoffFactor Y0 P b ≠ 0 →
        (G.interactionExponent sigma tau psi phi b).re +
            (gamma / 2) * (∑ e ∈ P, ‖G.bondField b e‖ ^ 2) ≤
          -((u ⬝ᵥ (A *ᵥ u)) / 2) + residual) :
    ‖G.innerIntegrand Y0 P sigma tau psi phi x b‖ ≤
      Real.exp
          (residual - gamma / 2 * G.threshold ^ 2 * (P.card : ℝ)) *
        cmp116Eq223RealGaussian A r u := by
  by_cases hcutoff : G.cutoffFactor Y0 P b = 0
  · simp only [CMP116Eq214AnalyticData.innerIntegrand, hcutoff, mul_zero,
      zero_mul, norm_zero, cmp116Eq223RealGaussian]
    exact mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
  · exact
      G.norm_innerIntegrand_le_exp_residual_sub_cardPenalty_mul_realGaussian
        Y0 P sigma tau psi phi x b u A r gamma residual
        hgamma hthreshold hinner (hinteraction hcutoff)

/-- Finite-coordinate almost-everywhere domination with an interaction
estimate required only on the support of the literal cutoff. -/
theorem CMP116Eq214FiniteGaussianData.ae_norm_innerIntegrand_le_exp_residual_sub_cardPenalty_mul_realGaussian_of_cutoffSupport
    {nDelta nY lieDim : ℕ} {Bond Ψ Φ E : Type*}
    [Fintype Bond] [Norm E]
    (G : CMP116Eq214FiniteGaussianData nDelta nY Bond Ψ Φ E lieDim)
    (Y0 P : Finset Bond)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : Ψ) (phi : Φ)
    (x : CMP116Eq214GaussianCoordinate Bond lieDim)
    (A : Matrix (Bond × Fin lieDim) (Bond × Fin lieDim) ℝ)
    (r : Bond × Fin lieDim → ℝ) (gamma residual : ℝ)
    (hgamma : 0 ≤ gamma) (hthreshold : 0 ≤ G.threshold)
    (hinner : ∀ b,
      ‖G.innerWeight sigma tau psi phi x b‖ ≤
        Real.exp (∑ i, r i * b i))
    (hinteraction : ∀ b,
      G.toAnalyticData.cutoffFactor Y0 P b ≠ 0 →
        (G.interactionExponent sigma tau psi phi b).re +
            (gamma / 2) * (∑ e ∈ P, ‖G.bondField b e‖ ^ 2) ≤
          -((b ⬝ᵥ (A *ᵥ b)) / 2) + residual) :
    ∀ᵐ b ∂matrixGaussianPi (G.covarianceRoot sigma tau),
      ‖G.toAnalyticData.innerIntegrand Y0 P sigma tau psi phi x b‖ ≤
        Real.exp
            (residual - gamma / 2 * G.threshold ^ 2 * (P.card : ℝ)) *
          cmp116Eq223RealGaussian A r b := by
  filter_upwards [] with b
  exact
    G.toAnalyticData.norm_innerIntegrand_le_exp_residual_sub_cardPenalty_mul_realGaussian_of_cutoffSupport
      Y0 P sigma tau psi phi x b b A r gamma residual
        hgamma hthreshold (hinner b) (hinteraction b)

/-- Almost-everywhere version of the cutoff-support contract.  This is the
source-faithful interface for a conditioned Gaussian: support of the
covariance and support of the literal cutoff may both be used without
strengthening either statement to every ambient coordinate. -/
theorem CMP116Eq214FiniteGaussianData.ae_norm_innerIntegrand_le_exp_residual_sub_cardPenalty_mul_realGaussian_of_ae_cutoffSupport
    {nDelta nY lieDim : ℕ} {Bond Ψ Φ E : Type*}
    [Fintype Bond] [Norm E]
    (G : CMP116Eq214FiniteGaussianData nDelta nY Bond Ψ Φ E lieDim)
    (Y0 P : Finset Bond)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : Ψ) (phi : Φ)
    (x : CMP116Eq214GaussianCoordinate Bond lieDim)
    (A : Matrix (Bond × Fin lieDim) (Bond × Fin lieDim) ℝ)
    (r : Bond × Fin lieDim → ℝ) (gamma residual : ℝ)
    (hgamma : 0 ≤ gamma) (hthreshold : 0 ≤ G.threshold)
    (hinner : ∀ b,
      ‖G.innerWeight sigma tau psi phi x b‖ ≤
        Real.exp (∑ i, r i * b i))
    (hinteraction :
      ∀ᵐ b ∂matrixGaussianPi (G.covarianceRoot sigma tau),
        G.toAnalyticData.cutoffFactor Y0 P b ≠ 0 →
          (G.interactionExponent sigma tau psi phi b).re +
              (gamma / 2) * (∑ e ∈ P, ‖G.bondField b e‖ ^ 2) ≤
            -((b ⬝ᵥ (A *ᵥ b)) / 2) + residual) :
    ∀ᵐ b ∂matrixGaussianPi (G.covarianceRoot sigma tau),
      ‖G.toAnalyticData.innerIntegrand Y0 P sigma tau psi phi x b‖ ≤
        Real.exp
            (residual - gamma / 2 * G.threshold ^ 2 * (P.card : ℝ)) *
          cmp116Eq223RealGaussian A r b := by
  filter_upwards [hinteraction] with b hb
  exact
    G.toAnalyticData.norm_innerIntegrand_le_exp_residual_sub_cardPenalty_mul_realGaussian_of_cutoffSupport
      Y0 P sigma tau psi phi x b b A r gamma residual
        hgamma hthreshold (hinner b) hb

/-- Integrated equation-(2.22)--(2.24) bound from a support-sensitive
interaction estimate. -/
theorem CMP116Eq214FiniteGaussianData.norm_innerIntegral_le_exp_residual_sub_cardPenalty_mul_eq224Majorant_of_cutoffSupport
    {nDelta nY lieDim : ℕ} {Bond Ψ Φ E : Type*}
    [Fintype Bond] [DecidableEq Bond] [Norm E]
    (G : CMP116Eq214FiniteGaussianData nDelta nY Bond Ψ Φ E lieDim)
    (Y0 P : Finset Bond)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : Ψ) (phi : Φ)
    (x : CMP116Eq214GaussianCoordinate Bond lieDim)
    (A : Matrix (Bond × Fin lieDim) (Bond × Fin lieDim) ℝ)
    (r : Bond × Fin lieDim → ℝ) (gamma residual : ℝ)
    (hgamma : 0 ≤ gamma) (hthreshold : 0 ≤ G.threshold)
    (hpos :
      (1 + (G.covarianceRoot sigma tau)ᵀ * A *
        G.covarianceRoot sigma tau).PosDef)
    (hinner : ∀ b,
      ‖G.innerWeight sigma tau psi phi x b‖ ≤
        Real.exp (∑ i, r i * b i))
    (hinteraction : ∀ b,
      G.toAnalyticData.cutoffFactor Y0 P b ≠ 0 →
        (G.interactionExponent sigma tau psi phi b).re +
            (gamma / 2) * (∑ e ∈ P, ‖G.bondField b e‖ ^ 2) ≤
          -((b ⬝ᵥ (A *ᵥ b)) / 2) + residual) :
    ‖∫ b, G.toAnalyticData.innerIntegrand Y0 P sigma tau psi phi x b
        ∂G.toAnalyticData.conditionedMeasure sigma tau‖ ≤
      Real.exp
          (residual - gamma / 2 * G.threshold ^ 2 * (P.card : ℝ)) *
        cmp116Eq224GaussianMajorant (G.covarianceRoot sigma tau) A
          (fun i => (r i : ℂ)) := by
  rw [G.toAnalyticData_conditionedMeasure]
  let scale : ℝ := Real.exp
    (residual - gamma / 2 * G.threshold ^ 2 * (P.card : ℝ))
  have hgaussian := integrable_cmp116Eq223RealGaussian_matrixGaussianPi
    (G.covarianceRoot sigma tau) A hpos r
  have hscaled : Integrable (fun b => scale * cmp116Eq223RealGaussian A r b)
      (matrixGaussianPi (G.covarianceRoot sigma tau)) :=
    hgaussian.const_mul scale
  calc
    ‖∫ b, G.toAnalyticData.innerIntegrand Y0 P sigma tau psi phi x b
        ∂matrixGaussianPi (G.covarianceRoot sigma tau)‖ ≤
      ∫ b, scale * cmp116Eq223RealGaussian A r b
        ∂matrixGaussianPi (G.covarianceRoot sigma tau) :=
      norm_integral_le_of_norm_le hscaled
        (G.ae_norm_innerIntegrand_le_exp_residual_sub_cardPenalty_mul_realGaussian_of_cutoffSupport
          Y0 P sigma tau psi phi x A r gamma residual
            hgamma hthreshold hinner hinteraction)
    _ = scale *
        (∫ b, cmp116Eq223RealGaussian A r b
          ∂matrixGaussianPi (G.covarianceRoot sigma tau)) := by
      rw [integral_const_mul]
    _ = scale *
        cmp116Eq224GaussianMajorant
          (G.covarianceRoot sigma tau) A (fun i => (r i : ℂ)) := by
      rw [integral_cmp116Eq223RealGaussian_matrixGaussianPi_eq_majorant
        (G.covarianceRoot sigma tau) A hpos r]
    _ = Real.exp
          (residual - gamma / 2 * G.threshold ^ 2 * (P.card : ℝ)) *
        cmp116Eq224GaussianMajorant (G.covarianceRoot sigma tau) A
          (fun i => (r i : ℂ)) := rfl

/-- Integrated equation-(2.22)--(2.24) bound when the support-sensitive
interaction estimate itself is known almost everywhere for the conditioned
Gaussian. -/
theorem CMP116Eq214FiniteGaussianData.norm_innerIntegral_le_exp_residual_sub_cardPenalty_mul_eq224Majorant_of_ae_cutoffSupport
    {nDelta nY lieDim : ℕ} {Bond Ψ Φ E : Type*}
    [Fintype Bond] [DecidableEq Bond] [Norm E]
    (G : CMP116Eq214FiniteGaussianData nDelta nY Bond Ψ Φ E lieDim)
    (Y0 P : Finset Bond)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : Ψ) (phi : Φ)
    (x : CMP116Eq214GaussianCoordinate Bond lieDim)
    (A : Matrix (Bond × Fin lieDim) (Bond × Fin lieDim) ℝ)
    (r : Bond × Fin lieDim → ℝ) (gamma residual : ℝ)
    (hgamma : 0 ≤ gamma) (hthreshold : 0 ≤ G.threshold)
    (hpos :
      (1 + (G.covarianceRoot sigma tau)ᵀ * A *
        G.covarianceRoot sigma tau).PosDef)
    (hinner : ∀ b,
      ‖G.innerWeight sigma tau psi phi x b‖ ≤
        Real.exp (∑ i, r i * b i))
    (hinteraction :
      ∀ᵐ b ∂matrixGaussianPi (G.covarianceRoot sigma tau),
        G.toAnalyticData.cutoffFactor Y0 P b ≠ 0 →
          (G.interactionExponent sigma tau psi phi b).re +
              (gamma / 2) * (∑ e ∈ P, ‖G.bondField b e‖ ^ 2) ≤
            -((b ⬝ᵥ (A *ᵥ b)) / 2) + residual) :
    ‖∫ b, G.toAnalyticData.innerIntegrand Y0 P sigma tau psi phi x b
        ∂G.toAnalyticData.conditionedMeasure sigma tau‖ ≤
      Real.exp
          (residual - gamma / 2 * G.threshold ^ 2 * (P.card : ℝ)) *
        cmp116Eq224GaussianMajorant (G.covarianceRoot sigma tau) A
          (fun i => (r i : ℂ)) := by
  rw [G.toAnalyticData_conditionedMeasure]
  let scale : ℝ := Real.exp
    (residual - gamma / 2 * G.threshold ^ 2 * (P.card : ℝ))
  have hgaussian := integrable_cmp116Eq223RealGaussian_matrixGaussianPi
    (G.covarianceRoot sigma tau) A hpos r
  have hscaled : Integrable (fun b => scale * cmp116Eq223RealGaussian A r b)
      (matrixGaussianPi (G.covarianceRoot sigma tau)) :=
    hgaussian.const_mul scale
  calc
    ‖∫ b, G.toAnalyticData.innerIntegrand Y0 P sigma tau psi phi x b
        ∂matrixGaussianPi (G.covarianceRoot sigma tau)‖ ≤
      ∫ b, scale * cmp116Eq223RealGaussian A r b
        ∂matrixGaussianPi (G.covarianceRoot sigma tau) :=
      norm_integral_le_of_norm_le hscaled
        (G.ae_norm_innerIntegrand_le_exp_residual_sub_cardPenalty_mul_realGaussian_of_ae_cutoffSupport
          Y0 P sigma tau psi phi x A r gamma residual
            hgamma hthreshold hinner hinteraction)
    _ = scale *
        (∫ b, cmp116Eq223RealGaussian A r b
          ∂matrixGaussianPi (G.covarianceRoot sigma tau)) := by
      rw [integral_const_mul]
    _ = scale *
        cmp116Eq224GaussianMajorant
          (G.covarianceRoot sigma tau) A (fun i => (r i : ℂ)) := by
      rw [integral_cmp116Eq223RealGaussian_matrixGaussianPi_eq_majorant
        (G.covarianceRoot sigma tau) A hpos r]
    _ = Real.exp
          (residual - gamma / 2 * G.threshold ^ 2 * (P.card : ℝ)) *
        cmp116Eq224GaussianMajorant (G.covarianceRoot sigma tau) A
          (fun i => (r i : ℂ)) := rfl

end

end YangMills.RG
