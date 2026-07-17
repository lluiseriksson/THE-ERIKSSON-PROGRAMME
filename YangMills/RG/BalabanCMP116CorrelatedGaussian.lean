/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq223Gaussian

/-!
# CMP116 correlated Gaussian and exact whitening

This module returns from the standardized Gaussian coordinates used in
`BalabanCMP116Eq223Gaussian` to a finite-dimensional correlated Gaussian.
For a real matrix `R`, it defines

`matrixGaussianPi R = R_* standardGaussianPi`

and proves both exact whitening by `R⁻¹` when `R` is invertible and the full
quadratic-exponential integral under this correlated law.  Under the change of
variables `u = R x`, the quadratic matrix and complex bilinear source become

`A ↦ Rᵀ A R`,  `c ↦ Rᵀ c`.

This is the measure-transport step needed to consume the standardized
two-stage Gaussian calculation in the CMP116 (2.23)--(2.25) chain.  It
constructs the correlated law as a pushforward.  If a physical Gaussian is
specified independently by a density, determinant, or covariance operator,
its equality with this pushforward remains a separate source-identification
theorem.  No claim about the full term (2.14) or estimate (2.26) is made here.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators NNReal RealInnerProductSpace

namespace YangMills.RG

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Continuous linear realization of matrix-vector multiplication on a finite
real coordinate space. -/
noncomputable def matrixMulVecCLM (R : Matrix ι ι ℝ) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  LinearMap.toContinuousLinearMap R.mulVecLin

/-- The centered correlated Gaussian obtained by pushing the standard product
Gaussian through `R`. -/
noncomputable def matrixGaussianPi (R : Matrix ι ι ℝ) : Measure (ι → ℝ) :=
  (standardGaussianPi ι).map (matrixMulVecCLM R)

instance (R : Matrix ι ι ℝ) : IsProbabilityMeasure (matrixGaussianPi R) := by
  unfold matrixGaussianPi
  exact Measure.isProbabilityMeasure_map (by fun_prop)

theorem matrixMulVecCLM_apply (R : Matrix ι ι ℝ) (x : ι → ℝ) :
    matrixMulVecCLM R x = R *ᵥ x := rfl

/-- Exact whitening: an invertible covariance-root coordinate map followed by
its nonsingular inverse returns the standard Gaussian product measure. -/
theorem matrixGaussianPi_map_nonsing_inv
    [DecidableEq ι] (R : Matrix ι ι ℝ) (hR : IsUnit R) :
    (matrixGaussianPi R).map (matrixMulVecCLM R⁻¹) =
      standardGaussianPi ι := by
  letI := hR.invertible
  rw [matrixGaussianPi, Measure.map_map (by fun_prop) (by fun_prop)]
  have hcomp :
      (matrixMulVecCLM R⁻¹) ∘ (matrixMulVecCLM R) =
        id := by
    funext x
    simp only [Function.comp_apply, matrixMulVecCLM_apply, id_eq]
    rw [Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec]
  rw [hcomp, Measure.map_id]

/-- Pulling a real quadratic form through matrix-vector multiplication
conjugates its matrix by `Rᵀ` and `R`. -/
theorem matrixQuadraticForm_mulVec_eq
    (A R : Matrix ι ι ℝ) (x : ι → ℝ) :
    (R *ᵥ x) ⬝ᵥ (A *ᵥ (R *ᵥ x)) =
      x ⬝ᵥ ((Rᵀ * A * R) *ᵥ x) := by
  calc
    (R *ᵥ x) ⬝ᵥ (A *ᵥ (R *ᵥ x)) =
        x ⬝ᵥ (Rᵀ *ᵥ (A *ᵥ (R *ᵥ x))) := by
      symm
      rw [Matrix.dotProduct_mulVec x Rᵀ (A *ᵥ (R *ᵥ x))]
      rw [← Matrix.mulVec_transpose (Rᵀ) x]
      simp
    _ = x ⬝ᵥ ((Rᵀ * A * R) *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/-- A complex bilinear source pulled through a real matrix is transformed by
the complexification of the transpose.  There is no conjugation of `c`. -/
theorem matrixComplexSource_mulVec_eq
    (R : Matrix ι ι ℝ) (c : ι → ℂ) (x : ι → ℝ) :
    ∑ i, c i * ((R *ᵥ x) i : ℂ) =
      ∑ j, ((Rᵀ.map Complex.ofRealHom) *ᵥ c) j * (x j : ℂ) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply]
  push_cast
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [show Complex.ofRealHom (R j i) = (R j i : ℂ) from rfl]
  ring

/-- Exact quadratic-exponential integral under the correlated Gaussian
`matrixGaussianPi R`.  The result is the standardized symmetric-matrix formula
with the pulled-back quadratic matrix `Rᵀ A R` and source `Rᵀ c`. -/
theorem integral_cexp_symmetricQuadratic_matrixGaussianPi
    [DecidableEq ι]
    (R A : Matrix ι ι ℝ)
    (hpos : (1 + Rᵀ * A * R).PosDef)
    (c : ι → ℂ) :
    let AR : Matrix ι ι ℝ := Rᵀ * A * R
    let cR : ι → ℂ := (Rᵀ.map Complex.ofRealHom) *ᵥ c
    (∫ u : ι → ℝ,
        Complex.exp
          (-(((u ⬝ᵥ (A *ᵥ u) : ℝ) : ℂ) / 2) +
            ∑ i, c i * (u i : ℂ))
        ∂(matrixGaussianPi R)) =
      ((Real.sqrt (Matrix.det (1 + AR)))⁻¹ : ℝ) •
        Complex.exp
          ((cR ⬝ᵥ (((1 + AR)⁻¹).map Complex.ofRealHom *ᵥ cR)) / 2) := by
  dsimp only
  rw [matrixGaussianPi]
  rw [MeasureTheory.integral_map (by fun_prop) (by fun_prop)]
  have hfun :
      (fun x : ι → ℝ =>
        Complex.exp
          (-((((matrixMulVecCLM R x) ⬝ᵥ
              (A *ᵥ (matrixMulVecCLM R x)) : ℝ) : ℂ) / 2) +
            ∑ i, c i * ((matrixMulVecCLM R x) i : ℂ))) =
      (fun x : ι → ℝ =>
        Complex.exp
          (-(((x ⬝ᵥ ((Rᵀ * A * R) *ᵥ x) : ℝ) : ℂ) / 2) +
            ∑ j, ((Rᵀ.map Complex.ofRealHom) *ᵥ c) j * (x j : ℂ))) := by
    funext x
    rw [matrixMulVecCLM_apply, matrixQuadraticForm_mulVec_eq,
      matrixComplexSource_mulVec_eq]
  rw [hfun]
  exact integral_cexp_symmetricQuadratic_standardGaussianPi
    (Rᵀ * A * R) hpos ((Rᵀ.map Complex.ofRealHom) *ᵥ c)

end

end YangMills.RG
