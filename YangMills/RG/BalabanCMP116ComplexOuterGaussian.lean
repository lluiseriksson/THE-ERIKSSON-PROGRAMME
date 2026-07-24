/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116ComplexQuadraticSchur
import YangMills.RG.BalabanCMP116Eq223GaussianDomination

/-!
# Exact outer Gaussian for the CMP116 complex `R1`

The source-complex `R1` acts on the full outer Gaussian field.  Exponential
decay of its kernel does not turn this field into a coordinate-supported one:
a bound by the energy of a strict finite carrier would vanish on every vector
supported outside that carrier, while the nonlocal covariance sandwiches have
small but generally nonzero tails.

The source-faithful operation is therefore to integrate the global quadratic.
Only the symmetric part of the entrywise real matrix contributes on a real
field.  This module identifies that matrix exactly and evaluates its positive
real exponential against the standard product Gaussian.

The remaining quantitative obligation is deliberately explicit: factor the
symmetric real correction through the finite source-active state, prove the
shifted matrix positive definite, and bound the resulting determinant by the
active cardinality.  No coordinate-support or ambient-dimension claim is made.
-/

namespace YangMills.RG

open Matrix MeasureTheory
open scoped BigOperators

noncomputable section

/-- Symmetric real matrix governing the modulus of an analytic complex
quadratic on a real field. -/
def cmp116Eq214ComplexQuadraticSymmetricRealPart
    {ι : Type*} (A : Matrix ι ι ℂ) : Matrix ι ι ℝ :=
  (1 / 2 : ℝ) •
    (cmp116Eq214RealPartMatrix A +
      Matrix.transpose (cmp116Eq214RealPartMatrix A))

@[simp]
theorem cmp116Eq214ComplexQuadraticSymmetricRealPart_transpose
    {ι : Type*} (A : Matrix ι ι ℂ) :
    Matrix.transpose (cmp116Eq214ComplexQuadraticSymmetricRealPart A) =
      cmp116Eq214ComplexQuadraticSymmetricRealPart A := by
  ext i j
  simp [cmp116Eq214ComplexQuadraticSymmetricRealPart]
  ring

/-- A real quadratic form is unchanged by symmetrizing its matrix. -/
theorem dotProduct_symmetricRealPart_mulVec
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (x : ι → ℝ) :
    x ⬝ᵥ
        (cmp116Eq214ComplexQuadraticSymmetricRealPart A).mulVec x =
      x ⬝ᵥ (cmp116Eq214RealPartMatrix A).mulVec x := by
  let R := cmp116Eq214RealPartMatrix A
  have htranspose :
      x ⬝ᵥ (Matrix.transpose R).mulVec x =
        x ⬝ᵥ R.mulVec x := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
      dotProduct_comm]
  simp only [cmp116Eq214ComplexQuadraticSymmetricRealPart,
    Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul,
    dotProduct_add]
  change
    (1 / 2 : ℝ) •
        (x ⬝ᵥ R.mulVec x + x ⬝ᵥ (Matrix.transpose R).mulVec x) =
      x ⬝ᵥ R.mulVec x
  rw [htranspose]
  change
    (1 / 2 : ℝ) * (x ⬝ᵥ R.mulVec x + x ⬝ᵥ R.mulVec x) =
      x ⬝ᵥ R.mulVec x
  ring

/-- Exact real exponent controlling the norm of the analytic `R1` factor. -/
theorem cmp116Eq214ComplexQuadratic_re_eq_symmetricRealPart
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (x : ι → ℝ) :
    (cmp116Eq214ComplexQuadratic A x).re =
      (1 / 2 : ℝ) *
        (x ⬝ᵥ
          (cmp116Eq214ComplexQuadraticSymmetricRealPart A).mulVec x) := by
  rw [cmp116Eq214ComplexQuadratic_re,
    dotProduct_symmetricRealPart_mulVec]

/-- Exact standard-Gaussian integral of the modulus exponent of the global
source-complex quadratic.  This is the correct replacement for a false
pointwise localization of the outer field. -/
theorem integral_exp_re_complexQuadratic_standardGaussianPi
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ)
    (hpos :
      (1 - cmp116Eq214ComplexQuadraticSymmetricRealPart A).PosDef) :
    (∫ x : ι → ℝ,
        Real.exp ((cmp116Eq214ComplexQuadratic A x).re)
        ∂(standardGaussianPi ι)) =
      (Real.sqrt
        (Matrix.det
          (1 - cmp116Eq214ComplexQuadraticSymmetricRealPart A)))⁻¹ := by
  let H := cmp116Eq214ComplexQuadraticSymmetricRealPart A
  have hgaussian :
      (∫ x : ι → ℝ,
          cmp116Eq223RealGaussian (-H) 0 x
          ∂(matrixGaussianPi (1 : Matrix ι ι ℝ))) =
        cmp116Eq224GaussianMajorant
          (1 : Matrix ι ι ℝ) (-H) (fun _ => (0 : ℂ)) :=
    integral_cmp116Eq223RealGaussian_matrixGaussianPi_eq_majorant
      (1 : Matrix ι ι ℝ) (-H) (by simpa [H] using hpos) 0
  have hmeasure :
      matrixGaussianPi (1 : Matrix ι ι ℝ) = standardGaussianPi ι := by
    unfold matrixGaussianPi
    simpa [matrixMulVecCLM, Matrix.one_mulVec] using
      (Measure.map_id (standardGaussianPi ι))
  rw [hmeasure] at hgaussian
  calc
    (∫ x : ι → ℝ,
        Real.exp ((cmp116Eq214ComplexQuadratic A x).re)
        ∂(standardGaussianPi ι)) =
      ∫ x : ι → ℝ,
        cmp116Eq223RealGaussian (-H) 0 x
        ∂(standardGaussianPi ι) := by
          apply integral_congr_ae
          filter_upwards [] with x
          rw [cmp116Eq214ComplexQuadratic_re_eq_symmetricRealPart]
          change
            Real.exp ((1 / 2 : ℝ) * (x ⬝ᵥ H.mulVec x)) =
              cmp116Eq223RealGaussian (-H) 0 x
          simp only [cmp116Eq223RealGaussian, Pi.zero_apply,
            zero_mul, Finset.sum_const_zero, add_zero,
            Matrix.neg_mulVec, dotProduct_neg]
          congr 1
          ring
    _ = cmp116Eq224GaussianMajorant
          (1 : Matrix ι ι ℝ) (-H) (fun _ => (0 : ℂ)) := hgaussian
    _ = (Real.sqrt (Matrix.det (1 - H)))⁻¹ := by
      simp [cmp116Eq224GaussianMajorant, H, sub_eq_add_neg]

/-- Positivity of the shifted symmetric real part supplies integrability of
the exact global modulus exponent.  This prevents downstream callers from
reintroducing a separate integrability hypothesis. -/
theorem integrable_exp_re_complexQuadratic_standardGaussianPi
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ)
    (hpos :
      (1 - cmp116Eq214ComplexQuadraticSymmetricRealPart A).PosDef) :
    Integrable
      (fun x : ι → ℝ =>
        Real.exp ((cmp116Eq214ComplexQuadratic A x).re))
      (standardGaussianPi ι) := by
  let H := cmp116Eq214ComplexQuadraticSymmetricRealPart A
  have hexact :=
    integral_exp_re_complexQuadratic_standardGaussianPi A hpos
  have hdet :
      0 < Matrix.det (1 - H) := by
    exact hpos.det_pos
  have hrhs :
      (Real.sqrt (Matrix.det (1 - H)))⁻¹ ≠ 0 := by
    positivity
  by_contra hnot
  rw [integral_undef hnot] at hexact
  exact hrhs (by simpa [H] using hexact.symm)

/-- Exact-global-Gaussian domination theorem.  It replaces pointwise
localization of the outer field: a Banach-valued integrand may be dominated
directly by the modulus exponent of the full complex quadratic. -/
theorem norm_integral_le_of_exp_re_complexQuadratic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : Matrix ι ι ℂ)
    (hpos :
      (1 - cmp116Eq214ComplexQuadraticSymmetricRealPart A).PosDef)
    (C : ℝ) (f : (ι → ℝ) → F)
    (hf : ∀ᵐ x ∂standardGaussianPi ι,
      ‖f x‖ ≤
        C * Real.exp ((cmp116Eq214ComplexQuadratic A x).re)) :
    ‖∫ x, f x ∂standardGaussianPi ι‖ ≤
      C *
        (Real.sqrt
          (Matrix.det
            (1 - cmp116Eq214ComplexQuadraticSymmetricRealPart A)))⁻¹ := by
  have hint :=
    integrable_exp_re_complexQuadratic_standardGaussianPi A hpos
  calc
    ‖∫ x, f x ∂standardGaussianPi ι‖ ≤
        ∫ x,
          C * Real.exp ((cmp116Eq214ComplexQuadratic A x).re)
          ∂standardGaussianPi ι := by
      exact norm_integral_le_of_norm_le (hint.const_mul C) hf
    _ =
        C *
          (Real.sqrt
            (Matrix.det
              (1 - cmp116Eq214ComplexQuadraticSymmetricRealPart A)))⁻¹ := by
      rw [integral_const_mul,
        integral_exp_re_complexQuadratic_standardGaussianPi A hpos]

end

end YangMills.RG
