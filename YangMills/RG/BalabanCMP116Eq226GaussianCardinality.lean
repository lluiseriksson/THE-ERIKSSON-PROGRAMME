/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq225SourceEnergy
import YangMills.RG.BalabanCMP116Eq223PhysicalLocalizationProjector

/-!
# CMP116 equation (2.26): Gaussian cardinality factor

This module rewrites the exact outer Gaussian factor of (2.25) in the
polymer-volume language used by (2.26).  The localized-coordinate count is
already bounded by `M^d * d * (Nc^2 - 1) * |Z0|`; taking logarithms therefore
produces a completely explicit exponential cost per localization block.

Honest scope: this closes only the Gaussian cardinality contribution to
(2.26).  The `D`, `P`, `Z0'`, Cauchy-radius, kernel-residual, and subsequent
summability ledgers remain separate obligations.
-/

namespace YangMills.RG

open scoped Matrix.Norms.L2Operator

/-- Exact logarithmic form of the finite localized Gaussian moment. -/
theorem inv_sqrt_one_sub_two_mul_pow_eq_exp
    (beta : ℝ) (n : ℕ) (hbeta : 2 * beta < 1) :
    (Real.sqrt ((1 - 2 * beta) ^ n))⁻¹ =
      Real.exp (((n : ℝ) / 2) * (-Real.log (1 - 2 * beta))) := by
  have hq : 0 < 1 - 2 * beta := sub_pos.mpr hbeta
  rw [Real.sqrt_eq_rpow]
  rw [← Real.rpow_neg (pow_nonneg hq.le n)]
  rw [Real.rpow_def_of_pos (pow_pos hq n), Real.log_pow]
  congr 1
  ring

/-- A cardinality bound `n <= K*z` converts the exact Gaussian factor into
an exponential cost linear in `z`. -/
theorem inv_sqrt_one_sub_two_mul_pow_le_exp_card
    (beta : ℝ) (n K z : ℕ)
    (hbeta0 : 0 ≤ beta) (hbeta : 2 * beta < 1)
    (hn : n ≤ K * z) :
    (Real.sqrt ((1 - 2 * beta) ^ n))⁻¹ ≤
      Real.exp
        ((((K : ℝ) / 2) * (-Real.log (1 - 2 * beta))) * (z : ℝ)) := by
  rw [inv_sqrt_one_sub_two_mul_pow_eq_exp beta n hbeta]
  apply Real.exp_le_exp.mpr
  have hq0 : 0 ≤ 1 - 2 * beta := (sub_pos.mpr hbeta).le
  have hq1 : 1 - 2 * beta ≤ 1 := by linarith
  have hlog : 0 ≤ -Real.log (1 - 2 * beta) := by
    exact neg_nonneg.mpr (Real.log_nonpos hq0 hq1)
  calc
    (n : ℝ) / 2 * (-Real.log (1 - 2 * beta)) ≤
        ((K * z : ℕ) : ℝ) / 2 * (-Real.log (1 - 2 * beta)) := by
      apply mul_le_mul_of_nonneg_right _ hlog
      exact div_le_div_of_nonneg_right (by exact_mod_cast hn) (by norm_num)
    _ = ((K : ℝ) / 2 * (-Real.log (1 - 2 * beta))) * (z : ℝ) := by
      push_cast
      ring

namespace PhysicalGaugeCMP116Dictionary

variable {d M N' Nc L lieDim : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
variable [NeZero Nc] [NeZero L] [NeZero lieDim]

/-- Explicit Gaussian cost per localization block in equation (2.26). -/
noncomputable def cmp116Eq226GaussianCardinalityRate
    (M d Nc : ℕ) (beta : ℝ) : ℝ :=
  ((((M ^ d * d) * (Nc ^ 2 - 1) : ℕ) : ℝ) / 2) *
    (-Real.log (1 - 2 * beta))

/-- Combined per-block rate of the rank-localized determinant and the outer
source-energy moment. -/
noncomputable def cmp116Eq226TotalGaussianCardinalityRate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M d Nc : ℕ) (R : Matrix ι ι ℝ)
    (alpha sourceBeta : ℝ) : ℝ :=
  cmp116Eq226GaussianCardinalityRate M d Nc
      (alpha * ‖R‖ ^ 2 / 2) +
    cmp116Eq226GaussianCardinalityRate M d Nc sourceBeta

/-- Physical specialization: the exact (2.25) factor is at most
`exp(c_G * |Z0|)` with no hidden geometric constant. -/
theorem localizedGaussianFactor_le_exp_card_Z0
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (Z0 : Finset (FinBox d N'))
    (beta : ℝ) (hbeta0 : 0 ≤ beta) (hbeta : 2 * beta < 1) :
    (Real.sqrt
      ((1 - 2 * beta) ^
        (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0).card))⁻¹ ≤
      Real.exp
        (cmp116Eq226GaussianCardinalityRate M d Nc beta * (Z0.card : ℝ)) := by
  have hn :
      (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0).card ≤
        ((M ^ d * d) * (Nc ^ 2 - 1)) * Z0.card := by
    calc
      (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0).card ≤
          ((Z0.card * M ^ d) * d) * (Nc ^ 2 - 1) :=
        Dict.card_cmp116Eq223PhysicalLocalizedCoordinates_le Z0
      _ = ((M ^ d * d) * (Nc ^ 2 - 1)) * Z0.card := by ring
  simpa [cmp116Eq226GaussianCardinalityRate] using
    inv_sqrt_one_sub_two_mul_pow_le_exp_card beta
      (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0).card
      ((M ^ d * d) * (Nc ^ 2 - 1)) Z0.card hbeta0 hbeta hn

/-- Both localized Gaussian cardinality factors are absorbed into one
explicit polymer-volume exponential. -/
theorem localizedGaussianProduct_le_exp_card_Z0
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (Z0 : Finset (FinBox d N'))
    (R : Matrix (CMP116CoordIndex d L lieDim)
      (CMP116CoordIndex d L lieDim) ℝ)
    (alpha sourceBeta : ℝ)
    (halpha : 0 ≤ alpha)
    (hsmall : alpha * ‖R‖ ^ 2 < 1)
    (hsourceBeta0 : 0 ≤ sourceBeta)
    (hsourceBeta : 2 * sourceBeta < 1) :
    (Real.sqrt
      ((1 - alpha * ‖R‖ ^ 2) ^
        (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0).card))⁻¹ *
      (Real.sqrt
        ((1 - 2 * sourceBeta) ^
          (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0).card))⁻¹ ≤
      Real.exp
        (cmp116Eq226TotalGaussianCardinalityRate M d Nc R alpha sourceBeta *
          (Z0.card : ℝ)) := by
  let detBeta := alpha * ‖R‖ ^ 2 / 2
  have hdetBeta0 : 0 ≤ detBeta := by
    unfold detBeta
    positivity
  have hdetBeta : 2 * detBeta < 1 := by
    unfold detBeta
    linarith
  have hdetBase : 1 - 2 * detBeta = 1 - alpha * ‖R‖ ^ 2 := by
    unfold detBeta
    ring
  have hdet := Dict.localizedGaussianFactor_le_exp_card_Z0
    Z0 detBeta hdetBeta0 hdetBeta
  have hsource := Dict.localizedGaussianFactor_le_exp_card_Z0
    Z0 sourceBeta hsourceBeta0 hsourceBeta
  calc
    (Real.sqrt
      ((1 - alpha * ‖R‖ ^ 2) ^
        (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0).card))⁻¹ *
        (Real.sqrt
          ((1 - 2 * sourceBeta) ^
            (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0).card))⁻¹ ≤
      Real.exp (cmp116Eq226GaussianCardinalityRate M d Nc detBeta *
          (Z0.card : ℝ)) *
        Real.exp (cmp116Eq226GaussianCardinalityRate M d Nc sourceBeta *
          (Z0.card : ℝ)) := by
      rw [← hdetBase]
      exact mul_le_mul hdet hsource (by positivity) (by positivity)
    _ = Real.exp
        (cmp116Eq226TotalGaussianCardinalityRate M d Nc R alpha sourceBeta *
          (Z0.card : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      simp only [cmp116Eq226TotalGaussianCardinalityRate, detBeta]
      ring

end PhysicalGaugeCMP116Dictionary
end YangMills.RG
