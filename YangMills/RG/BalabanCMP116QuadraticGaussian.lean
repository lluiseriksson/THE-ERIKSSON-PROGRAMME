/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# CMP116 quadratic Gaussian integral: diagonal stage

This module proves the exact one-dimensional and finite-product identities for
a diagonal quadratic perturbation of the standard Gaussian.  It isolates the
analytic stage used before the determinant expression around Balaban, CMP 116
(1988), equation (2.24).

Honest scope: the quadratic form is already diagonal.  This file does not yet
diagonalize a general symmetric operator, identify the product with a
determinant, construct the source term (2.14), or prove the termwise estimate
(2.26).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace YangMills.RG

noncomputable section

/-- Exact complex quadratic-exponential integral under the real standard
Gaussian.  The condition `-1 < a` is precisely positivity of the combined
quadratic coefficient `(1 + a) / 2`. -/
theorem integral_cexp_quadratic_standardGaussian
    (a : ℝ) (c : ℂ) (ha : -1 < a) :
    ∫ x : ℝ, Complex.exp (-((a : ℂ) / 2 * (x : ℂ) ^ 2) + c * x)
        ∂(gaussianReal 0 (1 : NNReal)) =
      ((Real.sqrt (2 * Real.pi))⁻¹ : ℝ) •
        (((Real.pi : ℂ) / (((1 + a : ℝ) : ℂ) / 2)) ^ (1 / 2 : ℂ) *
          Complex.exp (c ^ 2 / (4 * (((1 + a : ℝ) : ℂ) / 2)))) := by
  rw [integral_gaussianReal_eq_integral_smul
    (by norm_num : (1 : NNReal) ≠ 0)]
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_one, sub_zero, mul_one]
  simp_rw [mul_smul]
  rw [MeasureTheory.integral_smul]
  congr 1
  calc
    (∫ x : ℝ, Real.exp (-x ^ 2 / 2) •
        Complex.exp (-(↑a / 2 * (x : ℂ) ^ 2) + c * x)) =
      ∫ x : ℝ, Complex.exp
        (-(((1 + a : ℝ) : ℂ) / 2) * (x : ℂ) ^ 2 + c * x) := by
          apply integral_congr_ae
          filter_upwards [] with x
          rw [Complex.real_smul, Complex.ofReal_exp, ← Complex.exp_add]
          congr 1
          push_cast
          ring
    _ = ((Real.pi : ℂ) / (((1 + a : ℝ) : ℂ) / 2)) ^ (1 / 2 : ℂ) *
          Complex.exp (c ^ 2 / (4 * (((1 + a : ℝ) : ℂ) / 2))) := by
          have hb : (-(((1 + a : ℝ) : ℂ) / 2)).re < 0 := by
            norm_num
            linarith
          convert integral_cexp_quadratic hb c 0 using 1 <;> simp [div_neg]

private theorem standardGaussian_quadratic_prefactor_normalization
    (a : ℝ) (ha : -1 < a) :
    (((Real.sqrt (2 * Real.pi))⁻¹ : ℝ) : ℂ) *
        (((Real.pi : ℂ) / (((1 + a : ℝ) : ℂ) / 2)) ^ (1 / 2 : ℂ)) =
      (((Real.sqrt (1 + a))⁻¹ : ℝ) : ℂ) := by
  have hs : 0 < 1 + a := by linarith
  have harg :
      (Real.pi : ℂ) / (((1 + a : ℝ) : ℂ) / 2) =
        ((Real.pi / ((1 + a) / 2) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg]
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
  rw [← Complex.ofReal_cpow (by positivity : 0 ≤ Real.pi / ((1 + a) / 2))]
  norm_cast
  change (√(2 * Real.pi))⁻¹ *
      (Real.pi / ((1 + a) / 2)) ^ (1 / (2 : ℝ)) = (√(1 + a))⁻¹
  rw [← Real.sqrt_eq_rpow]
  rw [Real.sqrt_div Real.pi_pos.le]
  rw [Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ))]
  rw [Real.sqrt_div hs.le]
  field_simp [Real.sqrt_ne_zero'.mpr hs,
    Real.sqrt_ne_zero'.mpr Real.pi_pos]

/-- Determinant-ready normalization of the one-dimensional identity.  This
removes the intermediate `π`, real scalar-action, and complex-power factors. -/
theorem integral_cexp_quadratic_standardGaussian_normalized
    (a : ℝ) (c : ℂ) (ha : -1 < a) :
    ∫ x : ℝ, Complex.exp (-((a : ℂ) / 2 * (x : ℂ) ^ 2) + c * x)
        ∂(gaussianReal 0 (1 : NNReal)) =
      ((Real.sqrt (1 + a))⁻¹ : ℝ) •
        Complex.exp (c ^ 2 / (2 * (1 + a))) := by
  rw [integral_cexp_quadratic_standardGaussian a c ha]
  rw [Complex.real_smul, Complex.real_smul]
  calc
    (↑(√(2 * Real.pi))⁻¹ : ℂ) *
        (((Real.pi : ℂ) / (((1 + a : ℝ) : ℂ) / 2)) ^ (1 / 2 : ℂ) *
          Complex.exp (c ^ 2 / (4 * (((1 + a : ℝ) : ℂ) / 2)))) =
      ((↑(√(2 * Real.pi))⁻¹ : ℂ) *
        (((Real.pi : ℂ) / (((1 + a : ℝ) : ℂ) / 2)) ^ (1 / 2 : ℂ))) *
          Complex.exp (c ^ 2 / (4 * (((1 + a : ℝ) : ℂ) / 2))) := by ring
    _ = (((Real.sqrt (1 + a))⁻¹ : ℝ) : ℂ) *
          Complex.exp (c ^ 2 / (4 * (((1 + a : ℝ) : ℂ) / 2))) := by
      rw [standardGaussian_quadratic_prefactor_normalization a ha]
    _ = (((Real.sqrt (1 + a))⁻¹ : ℝ) : ℂ) *
          Complex.exp (c ^ 2 / (2 * (1 + a))) := by
      congr 1
      congr 1
      push_cast
      have hs : (1 + a : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (by linarith : 0 < 1 + a))
      field_simp
      ring

/-- Exact finite-product form of the diagonal quadratic Gaussian integral.

This is the source-facing pre-determinant form: every coordinate may have its
own real quadratic coefficient and complex linear coefficient. -/
theorem integral_cexp_diagonalQuadratic_standardGaussianPi
    {ι : Type*} [Fintype ι] (a : ι → ℝ) (c : ι → ℂ)
    (ha : ∀ i, -1 < a i) :
    ∫ x : ι → ℝ,
        Complex.exp
          (-∑ i, (a i : ℂ) / 2 * (x i : ℂ) ^ 2 +
            ∑ i, c i * x i)
        ∂(Measure.pi fun _ : ι => gaussianReal 0 (1 : NNReal)) =
      ∏ i,
        ((Real.sqrt (2 * Real.pi))⁻¹ : ℝ) •
          (((Real.pi : ℂ) / (((1 + a i : ℝ) : ℂ) / 2)) ^ (1 / 2 : ℂ) *
            Complex.exp
              ((c i) ^ 2 / (4 * (((1 + a i : ℝ) : ℂ) / 2)))) := by
  simp_rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
    Complex.exp_sum]
  calc
    (∫ x : ι → ℝ,
        ∏ i, Complex.exp
          (-((a i : ℂ) / 2 * (x i : ℂ) ^ 2) + c i * x i)
        ∂(Measure.pi fun _ : ι => gaussianReal 0 (1 : NNReal))) =
      ∏ i, ∫ x : ℝ,
        Complex.exp (-((a i : ℂ) / 2 * (x : ℂ) ^ 2) + c i * x)
          ∂(gaussianReal 0 (1 : NNReal)) :=
        MeasureTheory.integral_fintype_prod_eq_prod
          (E := fun _ : ι => ℝ)
          (μ := fun _ : ι => gaussianReal 0 (1 : NNReal))
          (fun i x => Complex.exp
            (-((a i : ℂ) / 2 * (x : ℂ) ^ 2) + c i * x))
    _ = _ := by
      congr with i
      exact integral_cexp_quadratic_standardGaussian (a i) (c i) (ha i)

/-- Determinant-ready finite-dimensional diagonal identity.  The scalar
prefactor is the inverse square root of the product of the shifted diagonal
coefficients, and the exponent contains the corresponding diagonal inverse. -/
theorem integral_cexp_diagonalQuadratic_standardGaussianPi_normalized
    {ι : Type*} [Fintype ι] (a : ι → ℝ) (c : ι → ℂ)
    (ha : ∀ i, -1 < a i) :
    ∫ x : ι → ℝ,
        Complex.exp
          (-∑ i, (a i : ℂ) / 2 * (x i : ℂ) ^ 2 +
            ∑ i, c i * x i)
        ∂(Measure.pi fun _ : ι => gaussianReal 0 (1 : NNReal)) =
      ((Real.sqrt (∏ i, (1 + a i)))⁻¹ : ℝ) •
        Complex.exp (∑ i, (c i) ^ 2 / (2 * (1 + a i))) := by
  rw [integral_cexp_diagonalQuadratic_standardGaussianPi a c ha]
  have hcoord : ∀ i,
      ((Real.sqrt (2 * Real.pi))⁻¹ : ℝ) •
          (((Real.pi : ℂ) / (((1 + a i : ℝ) : ℂ) / 2)) ^ (1 / 2 : ℂ) *
            Complex.exp ((c i) ^ 2 / (4 * (((1 + a i : ℝ) : ℂ) / 2)))) =
        ((Real.sqrt (1 + a i))⁻¹ : ℝ) •
          Complex.exp ((c i) ^ 2 / (2 * (1 + a i))) := by
    intro i
    exact (integral_cexp_quadratic_standardGaussian (a i) (c i) (ha i)).symm.trans
      (integral_cexp_quadratic_standardGaussian_normalized (a i) (c i) (ha i))
  simp_rw [hcoord, Complex.real_smul]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
  have hsqrt :
      Real.sqrt (∏ i, (1 + a i)) = ∏ i, Real.sqrt (1 + a i) := by
    simpa using Real.sqrt_prod (Finset.univ : Finset ι)
      (fun i _ => le_of_lt (by linarith [ha i] : 0 < 1 + a i))
  rw [hsqrt]
  congr 1
  norm_cast
  simp

end

end YangMills.RG
