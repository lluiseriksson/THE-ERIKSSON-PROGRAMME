/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251MultidimensionalAliasProduct

/-!
# PRE-VALIDATION: expanded alias geometry below CMP89 (2.51)

The source is present, but this module's `.olean` has not yet been
materialized and its results have not yet been verified by the compiler.

CMP89 (2.45), printed p. 584, uses `p' in [-pi,pi[` and a fixed centered set
of `N = L^j` integer aliases.  For even `N`, its half-open representative set
contains `-N/2`.  Consequently the literal scaled momentum of an extreme
alias need not remain in the central Brillouin interval: at
`N=2`, `p'=-pi`, `m=-1` its absolute value is `3*pi/2`.

This module records that obstruction as a theorem and proves the sharp
replacement needed downstream: every printed alias lies in the uniformly
expanded interval of radius `3*pi/2`.  Thus the central Jordan comparison
cannot be reused silently, while a separate expanded-zone estimate has an
honest, scale-uniform geometric input.

This module proves no averaging-symbol or Laplacian estimate and does not
complete the physical integrand comparison in (2.51).

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- Membership in the printed centered alias set gives the exact half-width
bound `2*|m| <= N`, including the asymmetric even branch. -/
theorem two_mul_abs_int_le_of_mem_cmp89Eq245CenteredAliasIntegers
    {N : ℕ} {m : ℤ} (hm : m ∈ cmp89Eq245CenteredAliasIntegers N) :
    2 * |m| ≤ (N : ℤ) := by
  rw [cmp89Eq245CenteredAliasIntegers] at hm
  split at hm
  · rw [Finset.mem_Ico] at hm
    by_cases hm0 : 0 ≤ m
    · rw [abs_of_nonneg hm0]
      omega
    · rw [abs_of_neg (lt_of_not_ge hm0)]
      omega
  · rw [Finset.mem_Icc] at hm
    by_cases hm0 : 0 ≤ m
    · rw [abs_of_nonneg hm0]
      omega
    · rw [abs_of_neg (lt_of_not_ge hm0)]
      omega

/-- Real form of the exact centered half-width bound. -/
theorem two_mul_abs_cast_le_of_mem_cmp89Eq245CenteredAliasIntegers
    {N : ℕ} {m : ℤ} (hm : m ∈ cmp89Eq245CenteredAliasIntegers N) :
    (2 : ℝ) * |(m : ℝ)| ≤ (N : ℝ) := by
  exact_mod_cast
    two_mul_abs_int_le_of_mem_cmp89Eq245CenteredAliasIntegers hm

/-- A literal source alias has unscaled magnitude at most `pi*(N+1)` on the
central momentum interval. -/
theorem abs_add_cmp89Eq245AliasShift_le_pi_mul_succ
    {N : ℕ} {m : ℤ} (hm : m ∈ cmp89Eq245CenteredAliasIntegers N)
    {p : ℝ} (hp : |p| ≤ Real.pi) :
    |p + 2 * Real.pi * (m : ℝ)| ≤ Real.pi * ((N : ℝ) + 1) := by
  have hmReal :=
    two_mul_abs_cast_le_of_mem_cmp89Eq245CenteredAliasIntegers hm
  calc
    |p + 2 * Real.pi * (m : ℝ)| ≤
        |p| + |2 * Real.pi * (m : ℝ)| := abs_add _ _
    _ = |p| + Real.pi * (2 * |(m : ℝ)|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2),
        abs_of_pos Real.pi_pos]
      ring
    _ ≤ Real.pi + Real.pi * (N : ℝ) := by
      gcongr
    _ = Real.pi * ((N : ℝ) + 1) := by ring

/-- Every alias in the fixed representative set of CMP89 (2.45) lies in the
uniformly expanded scaled interval of radius `3*pi/2`. -/
theorem abs_inverse_count_mul_add_cmp89Eq245AliasShift_le_three_pi_div_two
    {N : ℕ} (hN : 0 < N) {m : ℤ}
    (hm : m ∈ cmp89Eq245CenteredAliasIntegers N)
    {p : ℝ} (hp : |p| ≤ Real.pi) :
    |((N : ℝ)⁻¹ * (p + 2 * Real.pi * (m : ℝ)))| ≤
      3 * Real.pi / 2 := by
  by_cases hN1 : N = 1
  · subst N
    have hm0 : m = 0 := by
      rw [cmp89Eq245CenteredAliasIntegers] at hm
      norm_num at hm
      omega
    subst m
    simpa using hp.trans (by nlinarith [Real.pi_pos] : Real.pi ≤ 3 * Real.pi / 2)
  · have hN2 : 2 ≤ N := by omega
    have hNReal : 0 < (N : ℝ) := by exact_mod_cast hN
    have hraw := abs_add_cmp89Eq245AliasShift_le_pi_mul_succ hm hp
    rw [abs_mul, abs_inv, abs_of_pos hNReal, inv_mul_eq_div]
    apply (div_le_iff₀ hNReal).2
    calc
      |p + 2 * Real.pi * (m : ℝ)| ≤
          Real.pi * ((N : ℝ) + 1) := hraw
      _ ≤ (3 * Real.pi / 2) * (N : ℝ) := by
        have hNReal2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
        nlinarith [Real.pi_pos]

/-- The fixed even alias window is not pointwise contained in the central
scaled Brillouin interval.  This forbids silently applying the central-alias
Jordan estimate to every noncentral source alias. -/
theorem cmp89Eq245CenteredAliasIntegers_not_pointwise_scaled_brillouin :
    ∃ (N : ℕ) (p : ℝ) (m : ℤ),
      0 < N ∧ |p| ≤ Real.pi ∧
      m ∈ cmp89Eq245CenteredAliasIntegers N ∧
      Real.pi < |((N : ℝ)⁻¹ * (p + 2 * Real.pi * (m : ℝ)))| := by
  refine ⟨2, -Real.pi, -1, by norm_num, ?_, ?_, ?_⟩
  · simp [Real.pi_pos.le]
  · simp [cmp89Eq245CenteredAliasIntegers]
  · rw [show ((2 : ℕ) : ℝ) = 2 by norm_num]
    have hpi : 0 < Real.pi := Real.pi_pos
    rw [show ((-1 : ℤ) : ℝ) = -1 by norm_num]
    simp only [invOf_eq_inv, abs_mul, abs_inv, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    nlinarith [abs_of_neg (by nlinarith : -Real.pi + 2 * Real.pi * (-1) < 0)]

end

end YangMills.RG
