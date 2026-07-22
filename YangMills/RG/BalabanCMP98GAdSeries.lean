/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98NoncommutativeExpFDeriv

/-!
# Balaban's `g(ad Y)` series from CMP98 (32)--(33)

CMP98 fixes the convention

`g(z) = sum n, (-1)^n z^n/(n+1)! = (1 - exp(-z))/z`.

This file defines the commutator as a continuous real-linear operator and
constructs the corresponding entire operator series.  The sign is part of
the definition: the linear term is `-(1/2) ad Y`.

The next module identifies this series with the left-trivialized ordered
derivative of the noncommutative exponential.  No inverse `g(ad Y)⁻¹` is
postulated here.
-/

namespace YangMills.RG

open scoped BigOperators RightActions

noncomputable section

variable {𝔸 : Type*}
variable [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- The continuous commutator operator `H |-> YH - HY`. -/
def cmp98AdCLM (Y : 𝔸) : 𝔸 →L[ℝ] 𝔸 :=
  Y •> ContinuousLinearMap.id ℝ 𝔸 -
    ContinuousLinearMap.id ℝ 𝔸 <• Y

@[simp] theorem cmp98AdCLM_apply (Y H : 𝔸) :
    cmp98AdCLM Y H = Y * H - H * Y := by
  simp [cmp98AdCLM]

/-- The commutator costs at most twice the background norm. -/
theorem norm_cmp98AdCLM_le (Y : 𝔸) :
    ‖cmp98AdCLM Y‖ ≤ 2 * ‖Y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro H
  rw [cmp98AdCLM_apply]
  calc
    ‖Y * H - H * Y‖ ≤ ‖Y * H‖ + ‖H * Y‖ := norm_sub_le _ _
    _ ≤ ‖Y‖ * ‖H‖ + ‖H‖ * ‖Y‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = (2 * ‖Y‖) * ‖H‖ := by ring

/-- The `n`-th term of Balaban's entire function `g(ad Y)`. -/
def cmp98GAdTerm (Y : 𝔸) (n : ℕ) : 𝔸 →L[ℝ] 𝔸 :=
  (((-1 : ℝ) ^ n) / (n + 1).factorial) • (cmp98AdCLM Y) ^ n

theorem cmp98GAdTerm_apply (Y H : 𝔸) (n : ℕ) :
    cmp98GAdTerm Y n H =
      (((-1 : ℝ) ^ n) / (n + 1).factorial) •
        ((cmp98AdCLM Y) ^ n) H := by
  rfl

@[simp] theorem cmp98GAdTerm_zero (Y : 𝔸) :
    cmp98GAdTerm Y 0 = ContinuousLinearMap.id ℝ 𝔸 := by
  ext H
  simp [cmp98GAdTerm]

/-- The first correction has the source sign `-(1/2) ad Y`. -/
theorem cmp98GAdTerm_one (Y : 𝔸) :
    cmp98GAdTerm Y 1 = (-1 / 2 : ℝ) • cmp98AdCLM Y := by
  norm_num [cmp98GAdTerm]

/-- A shifted factorial coefficient is bounded by the ordinary exponential
coefficient. -/
theorem inv_succFactorial_le_inv_factorial (n : ℕ) :
    (((n + 1).factorial : ℝ))⁻¹ ≤ ((n.factorial : ℝ))⁻¹ := by
  apply inv_anti₀ (by positivity)
  exact_mod_cast Nat.factorial_le (Nat.le_succ n)

/-- Exponential majorant for every term of `g(ad Y)`. -/
theorem norm_cmp98GAdTerm_le (Y : 𝔸) (n : ℕ) :
    ‖cmp98GAdTerm Y n‖ ≤
      (2 * ‖Y‖) ^ n / n.factorial := by
  rcases n with _ | n
  · simpa [cmp98GAdTerm] using
      (ContinuousLinearMap.norm_id_le :
        ‖ContinuousLinearMap.id ℝ 𝔸‖ ≤ 1)
  rw [cmp98GAdTerm, norm_smul, Real.norm_eq_abs]
  have hfac0 : 0 ≤ ((n + 1 + 1).factorial : ℝ) := by positivity
  have hcoeff :
      |((-1 : ℝ) ^ (n + 1)) / ((n + 1 + 1).factorial : ℝ)| =
        (((n + 1 + 1).factorial : ℝ))⁻¹ := by
    rw [div_eq_mul_inv, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      one_mul, abs_of_nonneg (inv_nonneg.mpr hfac0)]
  rw [hcoeff]
  calc
    (((n + 1 + 1).factorial : ℝ))⁻¹ * ‖cmp98AdCLM Y ^ (n + 1)‖
        ≤ (((n + 1 + 1).factorial : ℝ))⁻¹ *
            ‖cmp98AdCLM Y‖ ^ (n + 1) := by
          exact mul_le_mul_of_nonneg_left
            (norm_pow_le' _ (Nat.succ_pos n)) (by positivity)
    _ ≤ (((n + 1 + 1).factorial : ℝ))⁻¹ *
          (2 * ‖Y‖) ^ (n + 1) := by
          gcongr
          exact norm_cmp98AdCLM_le Y
    _ ≤ (((n + 1).factorial : ℝ))⁻¹ *
          (2 * ‖Y‖) ^ (n + 1) := by
          exact mul_le_mul_of_nonneg_right
            (inv_succFactorial_le_inv_factorial (n + 1)) (by positivity)
    _ = (2 * ‖Y‖) ^ (n + 1) / (n + 1).factorial := by
      rw [div_eq_mul_inv]
      ring

/-- The source `g(ad Y)` series is absolutely summable for every `Y`. -/
theorem summable_cmp98GAdTerm (Y : 𝔸) :
    Summable (cmp98GAdTerm Y) := by
  apply Summable.of_norm
  exact (Real.summable_pow_div_factorial (2 * ‖Y‖)).of_nonneg_of_le
    (fun _ => norm_nonneg _)
    (fun n => norm_cmp98GAdTerm_le Y n)

/-- Balaban's entire operator `g(ad Y)` with the convention of CMP98
(32)--(33). -/
def cmp98GAd (Y : 𝔸) : 𝔸 →L[ℝ] 𝔸 :=
  ∑' n : ℕ, cmp98GAdTerm Y n

/-- The operator series may be evaluated term by term. -/
theorem cmp98GAd_apply (Y H : 𝔸) :
    cmp98GAd Y H = ∑' n : ℕ, cmp98GAdTerm Y n H := by
  unfold cmp98GAd
  exact (ContinuousLinearMap.apply ℝ 𝔸 H).map_tsum
    (summable_cmp98GAdTerm Y)

@[simp] theorem cmp98AdCLM_zero :
    cmp98AdCLM (0 : 𝔸) = 0 := by
  ext H
  simp

@[simp] theorem cmp98GAdTerm_zero_succ (n : ℕ) :
    cmp98GAdTerm (0 : 𝔸) (n + 1) = 0 := by
  simp [cmp98GAdTerm, cmp98AdCLM_zero, pow_succ]

/-- The source normalization `g(0)=1`. -/
@[simp] theorem cmp98GAd_zero :
    cmp98GAd (0 : 𝔸) = ContinuousLinearMap.id ℝ 𝔸 := by
  rw [cmp98GAd, (summable_cmp98GAdTerm (0 : 𝔸)).tsum_eq_zero_add]
  simp

end

end YangMills.RG
