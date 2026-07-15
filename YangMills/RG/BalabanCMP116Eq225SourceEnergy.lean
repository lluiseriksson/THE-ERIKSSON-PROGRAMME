/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq224SourceBound
import YangMills.RG.BalabanCMP116Eq225OuterGaussian
import YangMills.RG.BalabanCMP116Eq223CovarianceOpNorm

/-!
# CMP116 equations (2.24)--(2.25): energy-dependent source integration

The source produced by the inner Gaussian integration is linear in the outer
field, so a uniform source-norm bound is not the physically relevant
interface.  This module instead consumes the energy estimate

`‖r(X)‖² <= sourceRate * ∑ i ∈ S, X_i² + sourceResidual`.

It first turns the completed-square majorant of (2.24) into an exponential of
the localized outer energy.  It then integrates that exponential exactly with
the standard product Gaussian, producing the finite factor of (2.25).

Honest scope: the source-energy inequality and its uniform contour constants
remain hypotheses.  Identifying them with the concrete CMP116 `Γ_k` kernels,
factoring the resulting bound as (2.26), and closing `hraw`/`hRpoly` remain
open.
-/

open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

namespace YangMills.RG

noncomputable section

/-- Coefficient multiplying the source norm after completing the square in
equation (2.24). -/
def cmp116Eq225SourceCoefficient
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Matrix ι ι ℝ) (alpha : ℝ) : ℝ :=
  ‖R‖ ^ 2 / (2 * (1 - alpha * ‖R‖ ^ 2))

/-- Field-independent determinant and residual-source part of the (2.24)
majorant. -/
def cmp116Eq225SourceEnergyPrefactor
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Matrix ι ι ℝ) (alpha sourceResidual : ℝ) : ℝ :=
  (Real.sqrt ((1 - alpha * ‖R‖ ^ 2) ^ Fintype.card ι))⁻¹ *
    Real.exp (cmp116Eq225SourceCoefficient R alpha * sourceResidual)

/-- A source-energy estimate converts the (2.24) majorant into a localized
quadratic exponential in the outer field. -/
theorem cmp116Eq224_localized_gaussianMajorant_le_sourceEnergy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (R : Matrix ι ι ℝ) (alpha : ℝ)
    (r x : ι → ℝ) (sourceRate sourceResidual : ℝ)
    (halpha : 0 ≤ alpha)
    (hsmall : alpha * ‖R‖ ^ 2 < 1)
    (hsource : r ⬝ᵥ r ≤ sourceRate * (∑ i ∈ S, x i ^ 2) + sourceResidual) :
    cmp116Eq224GaussianMajorant R
        (-(alpha • cmp116Eq223CoordinateProjection S))
        (fun i => (r i : ℂ)) ≤
      cmp116Eq225SourceEnergyPrefactor R alpha sourceResidual *
        Real.exp
          ((cmp116Eq225SourceCoefficient R alpha * sourceRate) *
            ∑ i ∈ S, x i ^ 2) := by
  refine (cmp116Eq224_localized_gaussianMajorant_le
    S R alpha r halpha hsmall).trans ?_
  have hdenom : 0 < 2 * (1 - alpha * ‖R‖ ^ 2) := by
    have hd : 0 < 1 - alpha * ‖R‖ ^ 2 := sub_pos.mpr hsmall
    nlinarith
  have hcoeff : 0 ≤ cmp116Eq225SourceCoefficient R alpha := by
    unfold cmp116Eq225SourceCoefficient
    exact div_nonneg (sq_nonneg ‖R‖) hdenom.le
  unfold cmp116Eq225SourceEnergyPrefactor
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left
  · rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    unfold cmp116Eq225SourceCoefficient
    calc
      (‖R‖ ^ 2 * (r ⬝ᵥ r)) /
          (2 * (1 - alpha * ‖R‖ ^ 2)) =
        (‖R‖ ^ 2 /
          (2 * (1 - alpha * ‖R‖ ^ 2))) * (r ⬝ᵥ r) := by ring
      _ ≤
        (‖R‖ ^ 2 /
          (2 * (1 - alpha * ‖R‖ ^ 2))) *
          (sourceRate * ∑ i ∈ S, x i ^ 2 + sourceResidual) := by
            exact mul_le_mul_of_nonneg_left hsource hcoeff
      _ =
        (‖R‖ ^ 2 /
          (2 * (1 - alpha * ‖R‖ ^ 2))) * sourceResidual +
        ((‖R‖ ^ 2 /
          (2 * (1 - alpha * ‖R‖ ^ 2))) * sourceRate) *
          ∑ i ∈ S, x i ^ 2 := by ring
  · positivity

/-- Fixed-contour endpoint for (2.25).  It combines physical inner-Gaussian
domination, the source-energy estimate, and the exact outer Gaussian moment.
-/
theorem CMP116Eq214FiniteGaussianData.norm_analyticIntegrand_le_of_sourceEnergy
    {nDelta nY lieDim : ℕ} {Bond Ψ Φ E : Type*}
    [Fintype Bond] [DecidableEq Bond] [Norm E]
    (G : CMP116Eq214FiniteGaussianData nDelta nY Bond Ψ Φ E lieDim)
    (Y0 P : Finset Bond)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : Ψ) (phi : Φ)
    (S : Finset (Bond × Fin lieDim))
    (alpha sourceRate sourceResidual outerBound : ℝ)
    (r : CMP116Eq214GaussianCoordinate Bond lieDim →
      Bond × Fin lieDim → ℝ)
    (halpha : 0 ≤ alpha)
    (hsmall : alpha * ‖G.covarianceRoot sigma tau‖ ^ 2 < 1)
    (hbeta :
      2 * (cmp116Eq225SourceCoefficient (G.covarianceRoot sigma tau) alpha *
        sourceRate) < 1)
    (houter_nonneg : 0 ≤ outerBound)
    (houter : ∀ x, ‖G.outerWeight sigma tau psi phi x‖ ≤ outerBound)
    (hdom : ∀ x,
      ∀ᵐ b ∂matrixGaussianPi (G.covarianceRoot sigma tau),
        ‖G.toAnalyticData.innerIntegrand Y0 P sigma tau psi phi x b‖ ≤
          cmp116Eq223RealGaussian
            (-(alpha • cmp116Eq223CoordinateProjection S)) (r x) b)
    (hsource : ∀ x,
      (r x) ⬝ᵥ (r x) ≤
        sourceRate * (∑ i ∈ S, x i ^ 2) + sourceResidual) :
    ‖G.toAnalyticData.analyticIntegrand Y0 P sigma tau psi phi‖ ≤
      outerBound *
        (cmp116Eq225SourceEnergyPrefactor (G.covarianceRoot sigma tau)
          alpha sourceResidual *
        (Real.sqrt
          ((1 - 2 *
            (cmp116Eq225SourceCoefficient (G.covarianceRoot sigma tau) alpha *
              sourceRate)) ^ S.card))⁻¹) := by
  unfold CMP116Eq214AnalyticData.analyticIntegrand
  rw [G.toAnalyticData_mu0]
  unfold balabanCMP116Dmu0Flat
  rw [← mul_assoc]
  apply norm_integral_le_of_localizedGaussianEnergy
    S (cmp116Eq225SourceCoefficient (G.covarianceRoot sigma tau) alpha *
      sourceRate)
      (outerBound *
        cmp116Eq225SourceEnergyPrefactor (G.covarianceRoot sigma tau)
          alpha sourceResidual) hbeta
  filter_upwards [] with x
  rw [norm_mul]
  have hinner :=
    G.norm_innerIntegral_le_eq224Majorant_of_l2OpNormSmallness
      Y0 P sigma tau psi phi x S alpha (r x) halpha hsmall (hdom x)
  have hmajor := cmp116Eq224_localized_gaussianMajorant_le_sourceEnergy
    S (G.covarianceRoot sigma tau) alpha (r x) x sourceRate sourceResidual
      halpha hsmall (hsource x)
  calc
    ‖G.outerWeight sigma tau psi phi x‖ *
        ‖∫ b, G.toAnalyticData.innerIntegrand Y0 P sigma tau psi phi x b
          ∂G.toAnalyticData.conditionedMeasure sigma tau‖ ≤
      outerBound *
        cmp116Eq224GaussianMajorant (G.covarianceRoot sigma tau)
          (-(alpha • cmp116Eq223CoordinateProjection S))
          (fun i => ((r x) i : ℂ)) := by
            exact mul_le_mul (houter x) hinner (norm_nonneg _) houter_nonneg
    _ ≤ outerBound *
        (cmp116Eq225SourceEnergyPrefactor (G.covarianceRoot sigma tau)
          alpha sourceResidual *
        Real.exp
          ((cmp116Eq225SourceCoefficient (G.covarianceRoot sigma tau) alpha *
            sourceRate) * ∑ i ∈ S, x i ^ 2)) := by
          exact mul_le_mul_of_nonneg_left hmajor houter_nonneg
    _ = (outerBound *
        cmp116Eq225SourceEnergyPrefactor (G.covarianceRoot sigma tau)
          alpha sourceResidual) *
        Real.exp
          ((cmp116Eq225SourceCoefficient (G.covarianceRoot sigma tau) alpha *
            sourceRate) * ∑ i ∈ S, x i ^ 2) := by ring

end
end YangMills.RG
