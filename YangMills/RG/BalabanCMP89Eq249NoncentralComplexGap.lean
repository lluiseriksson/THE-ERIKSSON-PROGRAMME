/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq245EntireLaplacianVariation
import YangMills.RG.BalabanCMP89Eq249NoncentralRealGap

/-!
# Moment-dependent complex gap for noncentral CMP89 aliases

PRE-VALIDATION: source is present, the `.olean` has not yet been materialized,
and these results have not yet been verified by the compiler.

The mass-uniform real lower bound for a nonzero alias is stronger than the
global constant `1/9`: it is proportional to the squared shifted momentum.
Combining that bound with the sealed vertical variation of `Delta^xi` avoids
the false conclusion that the strip radius must shrink like the inverse alias
diameter.

This module is specialized to the physical dimension four.  It proves the
exact `l1 <= 2*l2` conversion, keeps the momentum-dependent budget visible,
and derives complex nonvanishing whenever that budget spends at most half of
the real gap.  It does not yet select a uniform radius, vary the averaging
quotient, sum aliases, construct `B0`, shift a contour or transport the result
to the regional Green function.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- In four dimensions, the coordinate `l1` norm is at most twice the
Euclidean norm used in CMP89 (2.51). -/
theorem sum_abs_le_two_mul_cmp89Eq251EuclideanNorm_fin_four
    (q : Fin 4 → ℝ) :
    (∑ mu, |q mu|) ≤ 2 * cmp89Eq251EuclideanNorm q := by
  have hsquare :
      (∑ mu, |q mu|) ^ 2 ≤ 4 * cmp89Eq251MomentumSquare q := by
    rw [Fin.sum_univ_four, cmp89Eq251MomentumSquare, Fin.sum_univ_four]
    nlinarith [
      sq_abs (q 0), sq_abs (q 1), sq_abs (q 2), sq_abs (q 3),
      sq_nonneg (|q 0| - |q 1|), sq_nonneg (|q 0| - |q 2|),
      sq_nonneg (|q 0| - |q 3|), sq_nonneg (|q 1| - |q 2|),
      sq_nonneg (|q 1| - |q 3|), sq_nonneg (|q 2| - |q 3|)]
  have hsum : 0 ≤ ∑ mu, |q mu| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hnorm : 0 ≤ cmp89Eq251EuclideanNorm q :=
    cmp89Eq251EuclideanNorm_nonneg q
  have hnormSq := sq_cmp89Eq251EuclideanNorm q
  nlinarith [sq_nonneg ((∑ mu, |q mu|) +
    2 * cmp89Eq251EuclideanNorm q)]

/-- Four-dimensional moment-dependent variation budget for the entire fine
symbol. -/
def cmp89Eq249NoncentralComplexGapBudget
    (rho : ℝ) (q : Fin 4 → ℝ) : ℝ :=
  let eps := rho * Real.exp rho
  eps * (4 * cmp89Eq251EuclideanNorm q + 4 * eps)

/-- The coordinatewise vertical budget is controlled by the physical
four-dimensional Euclidean momentum, with no alias diameter. -/
theorem cmp89Eq245EntireScaledLaplacianVerticalBudget_le_noncentralGapBudget
    {rho : ℝ} (hrho : 0 ≤ rho) {z : Fin 4 → ℂ} {q : Fin 4 → ℝ}
    (hreal : ∀ mu, (z mu).re = q mu) :
    cmp89Eq245EntireScaledLaplacianVerticalBudget 4 rho z ≤
      cmp89Eq249NoncentralComplexGapBudget rho q := by
  let eps := rho * Real.exp rho
  have heps : 0 ≤ eps := mul_nonneg hrho (Real.exp_pos rho).le
  have hl1 := sum_abs_le_two_mul_cmp89Eq251EuclideanNorm_fin_four q
  rw [cmp89Eq245EntireScaledLaplacianVerticalBudget,
    cmp89Eq249NoncentralComplexGapBudget]
  simp_rw [hreal]
  rw [Fin.sum_univ_four]
  have hl1' :
      |q 0| + |q 1| + |q 2| + |q 3| ≤
        2 * cmp89Eq251EuclideanNorm q := by
    simpa only [Fin.sum_univ_four] using hl1
  nlinarith

/-- A budget spending at most half of a positive real gap leaves half of that
gap in the complex norm. -/
theorem half_real_gap_le_norm_of_norm_sub_le_half
    {w : ℂ} {r gap : ℝ} (hr : 0 ≤ r) (hgap : gap ≤ r)
    (hvariation : ‖w - (r : ℂ)‖ ≤ gap / 2) :
    gap / 2 ≤ ‖w‖ := by
  have htri : ‖(r : ℂ)‖ ≤ ‖(r : ℂ) - w‖ + ‖w‖ := by
    calc
      ‖(r : ℂ)‖ = ‖((r : ℂ) - w) + w‖ := by ring_nf
      _ ≤ ‖(r : ℂ) - w‖ + ‖w‖ := norm_add_le _ _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
    norm_sub_rev] at htri
  nlinarith

/-- Every nonzero printed alias has a moment-dependent complex gap whenever
the explicit vertical budget spends at most half of the real CMP89 gap. -/
theorem half_momentum_gap_le_norm_cmp89Eq245EntireScaledLaplacianSymbol_noncentral
    {N : ℕ} (hN : 0 < N) {mass rho : ℝ} (hrho : 0 ≤ rho)
    {m : Fin 4 → ℤ}
    (hm : m ∈ cmp89Eq245CenteredAliasVectors 4 N) (hm0 : m ≠ 0)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu + 2 * Real.pi * (m mu : ℝ))
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (hbudget : cmp89Eq249NoncentralComplexGapBudget rho
        (fun mu => p mu + 2 * Real.pi * (m mu : ℝ)) ≤
      ((1 / (3 * Real.pi)) ^ 2 *
        cmp89Eq251MomentumSquare
          (fun mu => p mu + 2 * Real.pi * (m mu : ℝ))) / 2) :
    ((1 / (3 * Real.pi)) ^ 2 *
        cmp89Eq251MomentumSquare
          (fun mu => p mu + 2 * Real.pi * (m mu : ℝ))) / 2 ≤
      ‖cmp89Eq245EntireScaledLaplacianSymbol
        4 (N : ℝ)⁻¹ mass z‖ := by
  let q : Fin 4 → ℝ := fun mu => p mu + 2 * Real.pi * (m mu : ℝ)
  let realSymbol : ℝ :=
    cmp89Eq245ScaledLaplacianSymbol 4 (N : ℝ)⁻¹ mass q
  let gap : ℝ :=
    (1 / (3 * Real.pi)) ^ 2 * cmp89Eq251MomentumSquare q
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hxi : 0 < (N : ℝ)⁻¹ := inv_pos.mpr hNreal
  have hxi1 : (N : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hNreal]
    have hNone : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hN)
    exact_mod_cast hNone
  have hzone : ∀ mu, |(N : ℝ)⁻¹ * q mu| ≤ 3 * Real.pi / 2 := by
    intro mu
    exact abs_inverse_count_mul_add_cmp89Eq245AliasShift_le_three_pi_div_two
      hN (by
        rw [cmp89Eq245CenteredAliasVectors, Fintype.mem_piFinset] at hm
        exact hm mu) (hp mu)
  have hgapReal : gap ≤ realSymbol := by
    have hraw :=
      one_div_three_pi_sq_mul_momentumSquare_le_scaledLaplacian
        (d := 4) (xi := (N : ℝ)⁻¹) (mass := mass) (q := q) hxi hzone
    calc
      gap ≤ (1 / (3 * Real.pi)) ^ 2 *
          (cmp89Eq251MomentumSquare q + mass ^ 2) := by
        dsimp [gap]
        gcongr
        exact le_add_of_nonneg_right (sq_nonneg mass)
      _ ≤ realSymbol := by simpa [realSymbol] using hraw
  have hrealSymbol : 0 ≤ realSymbol := by
    dsimp [realSymbol]
    rw [cmp89Eq245ScaledLaplacianSymbol]
    exact add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)
  have hslice :
      cmp89Eq245EntireScaledLaplacianSymbol 4 (N : ℝ)⁻¹ mass
          (cmp89Eq245ComplexMomentumRealSlice z) =
        (realSymbol : ℂ) := by
    have hzslice :
        cmp89Eq245ComplexMomentumRealSlice z =
          fun mu => (q mu : ℂ) := by
      funext mu
      simp [cmp89Eq245ComplexMomentumRealSlice, hreal mu, q]
    rw [hzslice, cmp89Eq245EntireScaledLaplacianSymbol_ofReal_eq]
  have hvariationRaw :=
    norm_cmp89Eq245EntireScaledLaplacianSymbol_sub_realSlice_le
      hxi hxi1 hrho himag
  have hvariationBudget :=
    cmp89Eq245EntireScaledLaplacianVerticalBudget_le_noncentralGapBudget
      hrho hreal
  have hvariation :
      ‖cmp89Eq245EntireScaledLaplacianSymbol 4 (N : ℝ)⁻¹ mass z -
          (realSymbol : ℂ)‖ ≤ gap / 2 := by
    rw [← hslice]
    exact hvariationRaw.trans (hvariationBudget.trans (by simpa [q, gap] using hbudget))
  exact half_real_gap_le_norm_of_norm_sub_le_half
    hrealSymbol hgapReal hvariation

end

end YangMills.RG
