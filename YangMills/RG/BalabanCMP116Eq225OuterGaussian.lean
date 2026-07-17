/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116QuadraticGaussian

/-!
# CMP116 equation (2.25): the localized outer Gaussian moment

After the inner Gaussian integration in equations (2.23)--(2.24), the source
term is quadratic in the remaining real Gaussian field.  This module evaluates
the resulting outer moment exactly.  If `S` is the finite set of localized
coordinates and `2 * beta < 1`, then

`E exp(beta * ∑ i ∈ S, X_i^2) = (1 - 2 * beta)^(-|S|/2)`.

The last theorem packages the identity as a Bochner-integral domination bound.
It is the analytic mechanism needed to replace a nonphysical uniform-in-field
source bound by an energy estimate.

Honest scope: this module proves the exact standard-Gaussian step of (2.25).
It does not yet identify the concrete CMP116 source with a linear function of
the outer field, prove the corresponding source-energy estimate, factor the
result as (2.26), or close `hraw`/`hRpoly`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators

namespace YangMills.RG

noncomputable section

theorem integral_cexp_localizedEnergy_standardGaussianPi
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (beta : ℝ) (hbeta : 2 * beta < 1) :
    ∫ x : ι → ℝ,
        Complex.exp ((beta * ∑ i ∈ S, x i ^ 2 : ℝ) : ℂ)
        ∂(Measure.pi fun _ : ι => gaussianReal 0 (1 : NNReal)) =
      (((Real.sqrt ((1 - 2 * beta) ^ S.card))⁻¹ : ℝ) : ℂ) := by
  let a : ι → ℝ := fun i => if i ∈ S then -2 * beta else 0
  let c : ι → ℂ := fun _ => 0
  have ha : ∀ i, -1 < a i := by
    intro i
    simp only [a]
    split_ifs <;> linarith
  have h := integral_cexp_diagonalQuadratic_standardGaussianPi_normalized a c ha
  convert h using 1
  · apply integral_congr_ae
    filter_upwards [] with x
    congr 1
    simp [a, c]
    conv_rhs =>
      rw [← Finset.sum_subset (Finset.subset_univ S)
        (by intro i hi hnot; simp [hnot])]
    have hsum :
        (∑ i ∈ S,
          ((if i ∈ S then -(2 * beta) else 0 : ℝ) : ℂ) / 2 *
            (x i : ℂ) ^ 2) =
        ∑ i ∈ S, ((-(2 * beta) : ℝ) : ℂ) / 2 *
          (x i : ℂ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [if_pos hi]
    rw [hsum]
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    push_cast
    ring
  · simp [a, c]
    congr 1
    conv_rhs =>
      rw [← Finset.prod_subset (Finset.subset_univ S)
        (by intro i hi hnot; simp [hnot])]
    have hprod :
        (∏ i ∈ S, (1 + if i ∈ S then -(2 * beta) else 0)) =
          ∏ _i ∈ S, (1 - 2 * beta) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [if_pos hi]
      ring
    rw [hprod]
    simp

theorem integrable_exp_localizedEnergy_standardGaussianPi
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (beta : ℝ) (hbeta : 2 * beta < 1) :
    Integrable
      (fun x : ι → ℝ => Real.exp (beta * ∑ i ∈ S, x i ^ 2))
      (Measure.pi fun _ : ι => gaussianReal 0 (1 : NNReal)) := by
  have hexact := integral_cexp_localizedEnergy_standardGaussianPi S beta hbeta
  have hrhs : (Real.sqrt ((1 - 2 * beta) ^ S.card))⁻¹ ≠ 0 := by
    have : 0 < 1 - 2 * beta := sub_pos.mpr hbeta
    positivity
  have hc : Integrable
      (fun x : ι → ℝ =>
        Complex.exp ((beta * ∑ i ∈ S, x i ^ 2 : ℝ) : ℂ))
      (Measure.pi fun _ : ι => gaussianReal 0 (1 : NNReal)) := by
    by_contra hnot
    rw [integral_undef hnot] at hexact
    have hz : (((Real.sqrt ((1 - 2 * beta) ^ S.card))⁻¹ : ℝ) : ℂ) = 0 :=
      hexact.symm
    norm_cast at hz
  have hre := hc.re
  have heq :
      (fun x : ι → ℝ =>
        (Complex.exp ((beta * ∑ i ∈ S, x i ^ 2 : ℝ) : ℂ)).re) =
      (fun x : ι → ℝ => Real.exp (beta * ∑ i ∈ S, x i ^ 2)) := by
    funext x
    rw [Complex.exp_ofReal_re]
  rw [← heq]
  exact hre

theorem integral_exp_localizedEnergy_standardGaussianPi
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (beta : ℝ) (hbeta : 2 * beta < 1) :
    ∫ x : ι → ℝ, Real.exp (beta * ∑ i ∈ S, x i ^ 2)
        ∂(Measure.pi fun _ : ι => gaussianReal 0 (1 : NNReal)) =
      (Real.sqrt ((1 - 2 * beta) ^ S.card))⁻¹ := by
  apply Complex.ofReal_injective
  calc
    ((∫ x : ι → ℝ, Real.exp (beta * ∑ i ∈ S, x i ^ 2)
        ∂(Measure.pi fun _ : ι => gaussianReal 0 (1 : NNReal)) : ℝ) : ℂ) =
      ∫ x : ι → ℝ, (Real.exp (beta * ∑ i ∈ S, x i ^ 2) : ℂ)
        ∂(Measure.pi fun _ : ι => gaussianReal 0 (1 : NNReal)) := by
      symm
      exact integral_ofReal
    _ = ∫ x : ι → ℝ,
        Complex.exp ((beta * ∑ i ∈ S, x i ^ 2 : ℝ) : ℂ)
        ∂(Measure.pi fun _ : ι => gaussianReal 0 (1 : NNReal)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← Complex.ofReal_exp]
    _ = (((Real.sqrt ((1 - 2 * beta) ^ S.card))⁻¹ : ℝ) : ℂ) :=
      integral_cexp_localizedEnergy_standardGaussianPi S beta hbeta

theorem norm_integral_le_of_localizedGaussianEnergy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : Finset ι) (beta C : ℝ) (hbeta : 2 * beta < 1)
    (f : (ι → ℝ) → F)
    (hf : ∀ᵐ x ∂(Measure.pi fun _ : ι => gaussianReal 0 (1 : NNReal)),
      ‖f x‖ ≤ C * Real.exp (beta * ∑ i ∈ S, x i ^ 2)) :
    ‖∫ x, f x ∂(Measure.pi fun _ : ι => gaussianReal 0 (1 : NNReal))‖ ≤
      C * (Real.sqrt ((1 - 2 * beta) ^ S.card))⁻¹ := by
  have hint := integrable_exp_localizedEnergy_standardGaussianPi S beta hbeta
  calc
    ‖∫ x, f x ∂(Measure.pi fun _ : ι => gaussianReal 0 (1 : NNReal))‖ ≤
        ∫ x, C * Real.exp (beta * ∑ i ∈ S, x i ^ 2)
          ∂(Measure.pi fun _ : ι => gaussianReal 0 (1 : NNReal)) := by
      exact norm_integral_le_of_norm_le (hint.const_mul C) hf
    _ = C * (Real.sqrt ((1 - 2 * beta) ^ S.card))⁻¹ := by
      rw [integral_const_mul,
        integral_exp_localizedEnergy_standardGaussianPi S beta hbeta]

end
end YangMills.RG
