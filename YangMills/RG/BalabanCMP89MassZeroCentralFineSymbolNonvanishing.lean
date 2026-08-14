/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251NoncentralLaplacianRatio
import YangMills.RG.BalabanCMP89Eq249CentralStabilizedAliasDenominator

/-!
# PRE-VALIDATION: mass-zero central fine-symbol nonvanishing

Source is present, its `.olean` has not yet been materialized, and the result
has not yet been compiler-verified.

On the centered real cube, a nonzero momentum has strictly positive continuum
momentum square.  The already sealed expanded-zone comparison then makes the
mass-zero scaled lattice symbol strictly positive.  This is the central
counterpart of the existing noncentral-alias gap; it introduces no mass floor
and no arbitrary nonvanishing family.
-/

namespace YangMills.RG

noncomputable section

/-- A nonzero finite real momentum vector has positive Euclidean momentum
square. -/
theorem cmp89Eq251MomentumSquare_pos_of_ne_zero
    {d : ℕ} {p : Fin d → ℝ} (hp : p ≠ 0) :
    0 < cmp89Eq251MomentumSquare p := by
  have hex : ∃ mu, p mu ≠ 0 := by
    by_contra h
    push_neg at h
    exact hp (funext h)
  obtain ⟨mu, hmu⟩ := hex
  rw [cmp89Eq251MomentumSquare]
  apply Finset.sum_pos'
  · intro nu _
    exact sq_nonneg (p nu)
  · exact ⟨mu, Finset.mem_univ mu, sq_pos_of_ne_zero hmu⟩

/-- On the centered cube, every nonzero central momentum has strictly
positive mass-zero fine-lattice symbol at inverse integer spacing. -/
theorem cmp89Eq245ScaledLaplacianSymbol_massZero_pos_of_ne_zero
    {d N : ℕ} [NeZero N] {p : Fin d → ℝ}
    (hpCube : ∀ mu, |p mu| ≤ Real.pi) (hp : p ≠ 0) :
    0 < cmp89Eq245ScaledLaplacianSymbol d (N : ℝ)⁻¹ 0 p := by
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hxi : 0 < (N : ℝ)⁻¹ := inv_pos.mpr hN
  have hxiOne : (N : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hN]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have hzone : ∀ mu, |(N : ℝ)⁻¹ * p mu| ≤ 3 * Real.pi / 2 := by
    intro mu
    rw [abs_mul, abs_of_pos hxi]
    calc
      (N : ℝ)⁻¹ * |p mu| ≤ (N : ℝ)⁻¹ * Real.pi := by
        exact mul_le_mul_of_nonneg_left (hpCube mu) hxi.le
      _ ≤ 1 * Real.pi := by
        exact mul_le_mul_of_nonneg_right hxiOne Real.pi_pos.le
      _ ≤ 3 * Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hmomentum : 0 < cmp89Eq251MomentumSquare p :=
    cmp89Eq251MomentumSquare_pos_of_ne_zero hp
  have hlower :=
    one_div_three_pi_sq_mul_momentumSquare_le_scaledLaplacian
      (d := d) (xi := (N : ℝ)⁻¹) (mass := 0) (q := p) hxi hzone
  have hcoefficient : 0 < (1 / (3 * Real.pi)) ^ 2 := by positivity
  have hpositive :
      0 < (1 / (3 * Real.pi)) ^ 2 *
        (cmp89Eq251MomentumSquare p + (0 : ℝ) ^ 2) := by
    simpa only [zero_pow (by norm_num : 2 ≠ 0), add_zero] using
      mul_pos hcoefficient hmomentum
  exact hpositive.trans_le hlower

/-- Complex real-slice form used by the stabilized alias denominator. -/
theorem cmp89Eq249CentralEntireFineSymbol_massZero_ne_zero_ofReal
    {d N : ℕ} [NeZero N] {p : Fin d → ℝ}
    (hpCube : ∀ mu, |p mu| ≤ Real.pi) (hp : p ≠ 0) :
    cmp89Eq249CentralEntireFineSymbol d N 1 0
        (fun mu => (p mu : ℂ)) ≠ 0 := by
  have hpos :=
    cmp89Eq245ScaledLaplacianSymbol_massZero_pos_of_ne_zero
      (N := N) hpCube hp
  rw [cmp89Eq249CentralEntireFineSymbol,
    cmp89Eq245EntireScaledLaplacianSymbol_ofReal_eq]
  simpa only [pow_one, Nat.cast_id] using
    (Complex.ofReal_ne_zero.mpr (ne_of_gt hpos))

end

end YangMills.RG
