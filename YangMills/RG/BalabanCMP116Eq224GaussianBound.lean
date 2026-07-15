/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214IntegratedGaussianEstimate
import Mathlib.Analysis.Matrix.PosDef

/-!
# CMP116 equation (2.24): explicit norm of the correlated Gaussian integral

The existing correlated-Gaussian theorem evaluates the complex quadratic
integral exactly.  This module takes its norm and exposes the positive real
majorant used by the integrated-inner route for equation (2.14).  Unlike an
abstract `hinnerGaussian`, the bound below is computed from the determinant
and completed-square source term.
-/

namespace YangMills.RG

open MeasureTheory Matrix
open scoped RealInnerProductSpace

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- A positive-semidefinite perturbative Hessian stays positive semidefinite
after pullback by any covariance root, so adding the identity makes the
shifted Hessian strictly positive definite. -/
theorem posDef_one_add_transpose_mul_mul_of_posSemidef
    [DecidableEq ι]
    (R A : Matrix ι ι ℝ) (hA : A.PosSemidef) :
    (1 + Rᵀ * A * R).PosDef := by
  have hconj : (Rᴴ * A * R).PosSemidef :=
    hA.conjTranspose_mul_mul_same R
  have htranspose : Rᴴ = Rᵀ := by
    ext i j
    simp
  rw [htranspose] at hconj
  exact Matrix.PosDef.one.add_posSemidef hconj

/-- Explicit positive majorant produced by the correlated Gaussian identity. -/
noncomputable def cmp116Eq224GaussianMajorant
    [DecidableEq ι]
    (R A : Matrix ι ι ℝ) (c : ι → ℂ) : ℝ :=
  let AR : Matrix ι ι ℝ := Rᵀ * A * R
  let cR : ι → ℂ := (Rᵀ.map Complex.ofRealHom) *ᵥ c
  (Real.sqrt (Matrix.det (1 + AR)))⁻¹ *
    Real.exp
      ((cR ⬝ᵥ (((1 + AR)⁻¹).map Complex.ofRealHom *ᵥ cR) / 2).re)

/-- Positivity of the shifted Hessian makes the explicit Gaussian majorant
strictly positive. -/
theorem cmp116Eq224GaussianMajorant_pos
    [DecidableEq ι]
    (R A : Matrix ι ι ℝ)
    (hpos : (1 + Rᵀ * A * R).PosDef)
    (c : ι → ℂ) :
    0 < cmp116Eq224GaussianMajorant R A c := by
  simp only [cmp116Eq224GaussianMajorant]
  have hdet : 0 < Matrix.det (1 + Rᵀ * A * R) := hpos.det_pos
  exact mul_pos (inv_pos.mpr (Real.sqrt_pos.2 hdet)) (Real.exp_pos _)

/-- Taking the norm of the exact matrix-Gaussian identity gives the explicit
determinant/completed-square majorant of equation (2.24). -/
theorem norm_integral_cexp_symmetricQuadratic_matrixGaussianPi_eq_majorant
    [DecidableEq ι]
    (R A : Matrix ι ι ℝ)
    (hpos : (1 + Rᵀ * A * R).PosDef)
    (c : ι → ℂ) :
    ‖∫ u : ι → ℝ,
        Complex.exp
          (-(((u ⬝ᵥ (A *ᵥ u) : ℝ) : ℂ) / 2) +
            ∑ i, c i * (u i : ℂ))
        ∂(matrixGaussianPi R)‖ =
      cmp116Eq224GaussianMajorant R A c := by
  rw [integral_cexp_symmetricQuadratic_matrixGaussianPi R A hpos c]
  simp only [cmp116Eq224GaussianMajorant]
  have hdet : 0 < Matrix.det (1 + Rᵀ * A * R) := hpos.det_pos
  have hsqrt : 0 < Real.sqrt (Matrix.det (1 + Rᵀ * A * R)) :=
    Real.sqrt_pos.2 hdet
  rw [Complex.real_smul, norm_mul, Complex.norm_real, Complex.norm_exp,
    Real.norm_of_nonneg (inv_pos.mpr hsqrt).le]

/-- The exact identity, viewed as an upper bound in the shape consumed by
`hinnerGaussian`. -/
theorem norm_integral_cexp_symmetricQuadratic_matrixGaussianPi_le_majorant
    [DecidableEq ι]
    (R A : Matrix ι ι ℝ)
    (hpos : (1 + Rᵀ * A * R).PosDef)
    (c : ι → ℂ) :
    ‖∫ u : ι → ℝ,
        Complex.exp
          (-(((u ⬝ᵥ (A *ᵥ u) : ℝ) : ℂ) / 2) +
            ∑ i, c i * (u i : ℂ))
        ∂(matrixGaussianPi R)‖ ≤
      cmp116Eq224GaussianMajorant R A c := by
  exact le_of_eq
    (norm_integral_cexp_symmetricQuadratic_matrixGaussianPi_eq_majorant
      R A hpos c)

/-- If the integrated part of a literal (2.14) term is identified with the
quadratic Gaussian of (2.23), its norm is bounded by the explicit (2.24)
majorant.  This discharges one instance of `hinnerGaussian`; the identification
of the physical integrand remains visible as `hinner_eq`. -/
theorem CMP116Eq214FiniteGaussianData.norm_innerIntegral_le_eq224Majorant
    {nDelta nY lieDim : ℕ} {Bond Ψ Φ E : Type*}
    [Fintype Bond] [DecidableEq Bond] [Norm E]
    (G : CMP116Eq214FiniteGaussianData nDelta nY Bond Ψ Φ E lieDim)
    (Y0 P : Finset Bond)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : Ψ) (phi : Φ)
    (x : CMP116Eq214GaussianCoordinate Bond lieDim)
    (A : Matrix (Bond × Fin lieDim) (Bond × Fin lieDim) ℝ)
    (c : Bond × Fin lieDim → ℂ)
    (hpos :
      (1 + (G.covarianceRoot sigma tau)ᵀ * A *
        G.covarianceRoot sigma tau).PosDef)
    (hinner_eq : ∀ b,
      G.toAnalyticData.innerIntegrand Y0 P sigma tau psi phi x b =
        Complex.exp
          (-(((b ⬝ᵥ (A *ᵥ b) : ℝ) : ℂ) / 2) +
            ∑ i, c i * (b i : ℂ))) :
    ‖∫ b, G.toAnalyticData.innerIntegrand
        Y0 P sigma tau psi phi x b
        ∂G.toAnalyticData.conditionedMeasure sigma tau‖ ≤
      cmp116Eq224GaussianMajorant (G.covarianceRoot sigma tau) A c := by
  rw [G.toAnalyticData_conditionedMeasure]
  have hfun :
      (fun b => G.toAnalyticData.innerIntegrand
        Y0 P sigma tau psi phi x b) =
      (fun b => Complex.exp
        (-(((b ⬝ᵥ (A *ᵥ b) : ℝ) : ℂ) / 2) +
          ∑ i, c i * (b i : ℂ))) := by
    funext b
    exact hinner_eq b
  rw [hfun]
  exact norm_integral_cexp_symmetricQuadratic_matrixGaussianPi_le_majorant
    (G.covarianceRoot sigma tau) A hpos c

/-- End-to-end one-term consumer of equation (2.24).  Exact identification of
the inner integrand and a uniform bound on the explicit determinant/source
majorant replace the abstract `hinnerGaussian` premise. -/
theorem CMP116Eq214FiniteGaussianData.norm_term_le_cauchyRate_of_eq224Majorant
    {nDelta nY lieDim : ℕ} {Bond Ψ Φ E : Type*}
    [Fintype Bond] [DecidableEq Bond] [Norm E]
    (G : CMP116Eq214FiniteGaussianData nDelta nY Bond Ψ Φ E lieDim)
    (Y0 P : Finset Bond) (psi : Ψ) (phi : Φ)
    (outerBound innerGaussianBound : ℝ)
    (A : (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      CMP116Eq214GaussianCoordinate Bond lieDim →
        Matrix (Bond × Fin lieDim) (Bond × Fin lieDim) ℝ)
    (c : (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      CMP116Eq214GaussianCoordinate Bond lieDim →
        Bond × Fin lieDim → ℂ)
    (hDelta : ∀ i, 0 < G.deltaRadius i)
    (hY : ∀ i, 0 < G.yRadius i)
    (houter_nonneg : 0 ≤ outerBound)
    (houter : ∀ sigma tau x,
      ‖G.outerWeight sigma tau psi phi x‖ ≤ outerBound)
    (hpos : ∀ sigma tau x,
      (1 + (G.covarianceRoot sigma tau)ᵀ * A sigma tau x *
        G.covarianceRoot sigma tau).PosDef)
    (hinner_eq : ∀ sigma tau x b,
      G.toAnalyticData.innerIntegrand Y0 P sigma tau psi phi x b =
        Complex.exp
          (-(((b ⬝ᵥ ((A sigma tau x) *ᵥ b) : ℝ) : ℂ) / 2) +
            ∑ i, c sigma tau x i * (b i : ℂ)))
    (hmajorant : ∀ sigma tau x,
      cmp116Eq224GaussianMajorant (G.covarianceRoot sigma tau)
        (A sigma tau x) (c sigma tau x) ≤ innerGaussianBound) :
    ‖G.toAnalyticData.term Y0 P psi phi‖ ≤
      cmp116Eq214CauchyRate nDelta G.deltaRadius
        (cmp116Eq214CauchyRate nY G.yRadius
          (outerBound * innerGaussianBound)) := by
  apply G.norm_term_le_cauchyRate_of_innerGaussianIntegral
    Y0 P psi phi outerBound innerGaussianBound hDelta hY houter_nonneg houter
  intro sigma tau x
  exact (G.norm_innerIntegral_le_eq224Majorant
    Y0 P sigma tau psi phi x (A sigma tau x) (c sigma tau x)
    (hpos sigma tau x) (hinner_eq sigma tau x)).trans
      (hmajorant sigma tau x)

end

end YangMills.RG
