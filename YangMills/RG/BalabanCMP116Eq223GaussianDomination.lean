/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq224GaussianBound

/-!
# CMP116 equation (2.23): domination by an integrable real Gaussian

The physical integrand of equation (2.14) contains cutoffs and interaction
factors, so it need not equal the pure complex Gaussian evaluated in (2.24).
The correct bridge is pointwise domination of its norm by a positive real
Gaussian.  This module evaluates that dominant Gaussian exactly and propagates
the domination through the inner integral and the Cauchy estimate.

The remaining source obligation is explicit: prove the (2.20)--(2.22)
pointwise domination and integrability for the concrete CMP116 coefficients.
-/

namespace YangMills.RG

open MeasureTheory Matrix
open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Positive real Gaussian used on the right-hand side of (2.23). -/
noncomputable def cmp116Eq223RealGaussian
    (A : Matrix ι ι ℝ) (r : ι → ℝ) (u : ι → ℝ) : ℝ :=
  Real.exp (-((u ⬝ᵥ (A *ᵥ u)) / 2) + ∑ i, r i * u i)

/-- The positive real Gaussian in (2.23) has the same explicit determinant
and completed-square integral as the complex formula (2.24). -/
theorem integral_cmp116Eq223RealGaussian_matrixGaussianPi_eq_majorant
    [DecidableEq ι]
    (R A : Matrix ι ι ℝ)
    (hpos : (1 + Rᵀ * A * R).PosDef)
    (r : ι → ℝ) :
    (∫ u, cmp116Eq223RealGaussian A r u ∂matrixGaussianPi R) =
      cmp116Eq224GaussianMajorant R A (fun i => (r i : ℂ)) := by
  have hcomplex :=
    norm_integral_cexp_symmetricQuadratic_matrixGaussianPi_eq_majorant
      R A hpos (fun i => (r i : ℂ))
  have hnonneg :
      0 ≤ ∫ u, cmp116Eq223RealGaussian A r u ∂matrixGaussianPi R :=
    integral_nonneg fun _ => (Real.exp_pos _).le
  have hfun :
      (fun u : ι → ℝ => (cmp116Eq223RealGaussian A r u : ℂ)) =
      (fun u => Complex.exp
        (-(((u ⬝ᵥ (A *ᵥ u) : ℝ) : ℂ) / 2) +
          ∑ i, (r i : ℂ) * (u i : ℂ))) := by
    funext u
    rw [cmp116Eq223RealGaussian, Complex.ofReal_exp]
    congr 1
    push_cast
    rfl
  calc
    (∫ u, cmp116Eq223RealGaussian A r u ∂matrixGaussianPi R) =
        ‖((∫ u, cmp116Eq223RealGaussian A r u
          ∂matrixGaussianPi R : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_of_nonneg hnonneg]
    _ = ‖∫ u, Complex.exp
        (-(((u ⬝ᵥ (A *ᵥ u) : ℝ) : ℂ) / 2) +
          ∑ i, (r i : ℂ) * (u i : ℂ))
        ∂matrixGaussianPi R‖ := by
      congr 1
      rw [← integral_complex_ofReal, hfun]
    _ = cmp116Eq224GaussianMajorant R A (fun i => (r i : ℂ)) := hcomplex

/-- Integrability of the positive dominant Gaussian follows from the exact
integral and strict positivity of its determinant/source value.  If it were
not integrable, the Bochner integral would be zero, contradicting (2.24). -/
theorem integrable_cmp116Eq223RealGaussian_matrixGaussianPi
    [DecidableEq ι]
    (R A : Matrix ι ι ℝ)
    (hpos : (1 + Rᵀ * A * R).PosDef)
    (r : ι → ℝ) :
    Integrable (cmp116Eq223RealGaussian A r) (matrixGaussianPi R) := by
  by_contra hnot
  have hzero :
      (∫ u, cmp116Eq223RealGaussian A r u ∂matrixGaussianPi R) = 0 :=
    integral_undef hnot
  have heq :=
    integral_cmp116Eq223RealGaussian_matrixGaussianPi_eq_majorant
      R A hpos r
  have hmajorant_pos :=
    cmp116Eq224GaussianMajorant_pos R A hpos (fun i => (r i : ℂ))
  rw [hzero] at heq
  exact (ne_of_gt hmajorant_pos) heq.symm

/-- Pointwise domination by the real Gaussian of (2.23) produces the explicit
(2.24) bound on the inner integral. -/
theorem norm_integral_le_eq224Majorant_of_ae_le_realGaussian
    [DecidableEq ι]
    (R A : Matrix ι ι ℝ)
    (hpos : (1 + Rᵀ * A * R).PosDef)
    (r : ι → ℝ) (f : (ι → ℝ) → ℂ)
    (hdom : ∀ᵐ u ∂matrixGaussianPi R,
      ‖f u‖ ≤ cmp116Eq223RealGaussian A r u) :
    ‖∫ u, f u ∂matrixGaussianPi R‖ ≤
      cmp116Eq224GaussianMajorant R A (fun i => (r i : ℂ)) := by
  have hgaussian :=
    integrable_cmp116Eq223RealGaussian_matrixGaussianPi R A hpos r
  calc
    ‖∫ u, f u ∂matrixGaussianPi R‖ ≤
        ∫ u, cmp116Eq223RealGaussian A r u ∂matrixGaussianPi R :=
      norm_integral_le_of_norm_le hgaussian hdom
    _ = cmp116Eq224GaussianMajorant R A (fun i => (r i : ℂ)) :=
      integral_cmp116Eq223RealGaussian_matrixGaussianPi_eq_majorant
        R A hpos r

/-- Concrete (2.14) consumer: the cutoff/interacting inner integrand may be
different from the Gaussian, provided its norm is dominated by (2.23). -/
theorem CMP116Eq214FiniteGaussianData.norm_innerIntegral_le_eq224Majorant_of_domination
    {nDelta nY lieDim : ℕ} {Bond Ψ Φ E : Type*}
    [Fintype Bond] [DecidableEq Bond] [Norm E]
    (G : CMP116Eq214FiniteGaussianData nDelta nY Bond Ψ Φ E lieDim)
    (Y0 P : Finset Bond)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : Ψ) (phi : Φ)
    (x : CMP116Eq214GaussianCoordinate Bond lieDim)
    (A : Matrix (Bond × Fin lieDim) (Bond × Fin lieDim) ℝ)
    (r : Bond × Fin lieDim → ℝ)
    (hpos :
      (1 + (G.covarianceRoot sigma tau)ᵀ * A *
        G.covarianceRoot sigma tau).PosDef)
    (hdom : ∀ᵐ b ∂matrixGaussianPi (G.covarianceRoot sigma tau),
      ‖G.toAnalyticData.innerIntegrand
        Y0 P sigma tau psi phi x b‖ ≤
          cmp116Eq223RealGaussian A r b) :
    ‖∫ b, G.toAnalyticData.innerIntegrand
        Y0 P sigma tau psi phi x b
        ∂G.toAnalyticData.conditionedMeasure sigma tau‖ ≤
      cmp116Eq224GaussianMajorant (G.covarianceRoot sigma tau) A
        (fun i => (r i : ℂ)) := by
  rw [G.toAnalyticData_conditionedMeasure]
  exact norm_integral_le_eq224Majorant_of_ae_le_realGaussian
    (G.covarianceRoot sigma tau) A hpos r _ hdom

/-- End-to-end term estimate after the physical inequalities (2.20)--(2.22)
have supplied a real-Gaussian domination at every contour point. -/
theorem CMP116Eq214FiniteGaussianData.norm_term_le_cauchyRate_of_gaussianDomination
    {nDelta nY lieDim : ℕ} {Bond Ψ Φ E : Type*}
    [Fintype Bond] [DecidableEq Bond] [Norm E]
    (G : CMP116Eq214FiniteGaussianData nDelta nY Bond Ψ Φ E lieDim)
    (Y0 P : Finset Bond) (psi : Ψ) (phi : Φ)
    (outerBound innerGaussianBound : ℝ)
    (A : (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      CMP116Eq214GaussianCoordinate Bond lieDim →
        Matrix (Bond × Fin lieDim) (Bond × Fin lieDim) ℝ)
    (r : (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      CMP116Eq214GaussianCoordinate Bond lieDim →
        Bond × Fin lieDim → ℝ)
    (hDelta : ∀ i, 0 < G.deltaRadius i)
    (hY : ∀ i, 0 < G.yRadius i)
    (houter_nonneg : 0 ≤ outerBound)
    (houter : ∀ sigma tau x,
      ‖G.outerWeight sigma tau psi phi x‖ ≤ outerBound)
    (hpos : ∀ sigma tau x,
      (1 + (G.covarianceRoot sigma tau)ᵀ * A sigma tau x *
        G.covarianceRoot sigma tau).PosDef)
    (hdom : ∀ sigma tau x,
      ∀ᵐ b ∂matrixGaussianPi (G.covarianceRoot sigma tau),
        ‖G.toAnalyticData.innerIntegrand
          Y0 P sigma tau psi phi x b‖ ≤
            cmp116Eq223RealGaussian (A sigma tau x) (r sigma tau x) b)
    (hmajorant : ∀ sigma tau x,
      cmp116Eq224GaussianMajorant (G.covarianceRoot sigma tau)
        (A sigma tau x) (fun i => (r sigma tau x i : ℂ)) ≤
          innerGaussianBound) :
    ‖G.toAnalyticData.term Y0 P psi phi‖ ≤
      cmp116Eq214CauchyRate nDelta G.deltaRadius
        (cmp116Eq214CauchyRate nY G.yRadius
          (outerBound * innerGaussianBound)) := by
  apply G.norm_term_le_cauchyRate_of_innerGaussianIntegral
    Y0 P psi phi outerBound innerGaussianBound hDelta hY houter_nonneg houter
  intro sigma tau x
  exact (G.norm_innerIntegral_le_eq224Majorant_of_domination
    Y0 P sigma tau psi phi x (A sigma tau x) (r sigma tau x)
    (hpos sigma tau x) (hdom sigma tau x)).trans
      (hmajorant sigma tau x)

end

end YangMills.RG
