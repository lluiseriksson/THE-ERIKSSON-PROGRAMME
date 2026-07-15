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

end PhysicalGaugeCMP116Dictionary
end YangMills.RG
