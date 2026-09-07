/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq222CutoffSuppression
import YangMills.RG.BalabanCMP116MatrixGaussianCarrier

/-!
# Almost-everywhere interaction domination in CMP116 (2.22)

The conditioned Gaussian of equation (2.23) may live on a proper coordinate
carrier.  The interaction estimate is therefore needed only almost
everywhere under that Gaussian.  This module exposes that exact integral
interface while preserving the residual and large-field penalties.
-/

namespace YangMills.RG

open MeasureTheory Matrix

noncomputable section

/-- Integrated equations (2.20)--(2.24) with an almost-everywhere interaction
bound under the actual conditioned Gaussian. -/
theorem CMP116Eq214FiniteGaussianData.norm_innerIntegral_le_exp_residual_sub_cardPenalty_mul_eq224Majorant_of_ae
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
  have hdom :
      ∀ᵐ b ∂matrixGaussianPi (G.covarianceRoot sigma tau),
        ‖G.toAnalyticData.innerIntegrand
            Y0 P sigma tau psi phi x b‖ ≤
          scale * cmp116Eq223RealGaussian A r b := by
    filter_upwards [hinteraction] with b hb
    exact
      G.toAnalyticData
        |>.norm_innerIntegrand_le_exp_residual_sub_cardPenalty_mul_realGaussian
          Y0 P sigma tau psi phi x b b A r gamma residual
          hgamma hthreshold (hinner b) hb
  calc
    ‖∫ b, G.toAnalyticData.innerIntegrand Y0 P sigma tau psi phi x b
        ∂matrixGaussianPi (G.covarianceRoot sigma tau)‖ ≤
      ∫ b, scale * cmp116Eq223RealGaussian A r b
        ∂matrixGaussianPi (G.covarianceRoot sigma tau) :=
      norm_integral_le_of_norm_le hscaled hdom
    _ = scale *
        (∫ b, cmp116Eq223RealGaussian A r b
          ∂matrixGaussianPi (G.covarianceRoot sigma tau)) := by
      rw [integral_const_mul]
    _ = scale * cmp116Eq224GaussianMajorant
        (G.covarianceRoot sigma tau) A (fun i => (r i : ℂ)) := by
      rw [integral_cmp116Eq223RealGaussian_matrixGaussianPi_eq_majorant
        (G.covarianceRoot sigma tau) A hpos r]
    _ = Real.exp
          (residual - gamma / 2 * G.threshold ^ 2 * (P.card : ℝ)) *
        cmp116Eq224GaussianMajorant (G.covarianceRoot sigma tau) A
          (fun i => (r i : ℂ)) := rfl

end

end YangMills.RG
