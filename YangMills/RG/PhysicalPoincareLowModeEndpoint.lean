/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalPoincareLowModeBlock

/-!
# W-3 endpoint — the second Poincaré wall at coarse side two

This module assembles the exact W-3b Hodge identity and W-3c block identity
without division.  For the transverse square mode in dimension `d ≥ 3`,

`M · (⟪A,K₀A⟫ + ‖QA‖²) ≤ 5 · ‖A‖²`.

The quantifier order in `VolumeUniformQuotientPoincareGate` then contradicts
any fixed positive constant at `N' = 2`.  No statement for arbitrary coarse
side `N'` is made.

Oracle target: `[propext, Classical.choice, Quot.sound]`.  No sorry, no axioms.
-/

namespace YangMills.RG

open Matrix Module

/-- The W-3b identity with the half-side `M` in front:
`M · ⟪A,K₀A⟫ = 4 · ‖A‖²`. -/
theorem squareMode_mul_hodge_eq_four_norm_sq
    (d M Nc : ℕ) [NeZero d] [NeZero M] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (i j : Fin d) (w : SUNLieCoord Nc) :
    (M : ℝ) * inner ℝ (squareModeFine d M Nc i j w)
        (flatGaugeHodgeK0CLM d (M * 2) Nc ρ
          (squareModeFine d M Nc i j w)) =
      4 * ‖squareModeFine d M Nc i j w‖ ^ 2 := by
  change (M : ℝ) * inner ℝ (squareModeCochain d M Nc i j w)
      (flatGaugeHodgeK0CLM d (M * 2) Nc ρ
        (squareModeCochain d M Nc i j w)) =
    4 * ‖squareModeCochain d M Nc i j w‖ ^ 2
  have h := flatGaugeHodgeK0_squareMode_energy_mul_side
    d M Nc ρ i j w
  push_cast at h
  nlinarith

/-- For `d ≥ 3`, the transverse block contribution obeys the division-free
bound `M · ‖QA‖² ≤ ‖A‖²`. -/
theorem squareMode_mul_block_le_norm_sq
    (d M Nc : ℕ) [NeZero d] [NeZero M] [NeZero Nc]
    (hd : 3 ≤ d) (i j : Fin d) (hij : i ≠ j) (w : SUNLieCoord Nc) :
    (M : ℝ) *
        ‖flatBlockConstraintQCLM (d := d) (Nc := Nc) M 2
          (squareModeFine d M Nc i j w)‖ ^ 2 ≤
      ‖squareModeFine d M Nc i j w‖ ^ 2 := by
  rw [norm_sq_flatBlockConstraintQCLM_squareModeFine_of_ne
      d M Nc i j hij w,
    norm_sq_squareModeFine]
  have hM : (1 : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)
  have hpow : (M : ℝ) ^ 3 ≤ (M : ℝ) ^ d := by
    exact pow_le_pow_right₀ hM hd
  calc
    (M : ℝ) * ((2 : ℝ) ^ d * (M : ℝ) ^ 2 * ‖w‖ ^ 2) =
        ((2 : ℝ) ^ d * ‖w‖ ^ 2) * (M : ℝ) ^ 3 := by ring
    _ ≤ ((2 : ℝ) ^ d * ‖w‖ ^ 2) * (M : ℝ) ^ d :=
      mul_le_mul_of_nonneg_left hpow
        (mul_nonneg (pow_nonneg (by norm_num) d) (sq_nonneg ‖w‖))
    _ = (((M * 2 : ℕ) : ℝ) ^ d * ‖w‖ ^ 2) := by
      push_cast
      rw [mul_pow]
      ring

/-- The complete division-free W-3 energy bound. -/
theorem squareMode_mul_totalEnergy_le_five_norm_sq
    (d M Nc : ℕ) [NeZero d] [NeZero M] [NeZero Nc]
    (hd : 3 ≤ d) (ρ : SUNAdjointModel Nc)
    (i j : Fin d) (hij : i ≠ j) (w : SUNLieCoord Nc) :
    (M : ℝ) *
        (inner ℝ (squareModeFine d M Nc i j w)
            (flatGaugeHodgeK0CLM d (M * 2) Nc ρ
              (squareModeFine d M Nc i j w)) +
          ‖flatBlockConstraintQCLM (d := d) (Nc := Nc) M 2
            (squareModeFine d M Nc i j w)‖ ^ 2) ≤
      5 * ‖squareModeFine d M Nc i j w‖ ^ 2 := by
  have hH := squareMode_mul_hodge_eq_four_norm_sq
    d M Nc ρ i j w
  have hQ := squareMode_mul_block_le_norm_sq
    d M Nc hd i j hij w
  nlinarith

/-- **The second wall.**  In dimension at least three and for a nontrivial
internal fibre, the volume-uniform quotient Poincaré gate is false at fixed
coarse side `N' = 2`. -/
theorem volumeUniformQuotientPoincareGate_two_false
    {d Nc : ℕ} [NeZero d] [NeZero Nc]
    (hd : 3 ≤ d) (hNc : 2 ≤ Nc) (ρ : SUNAdjointModel Nc) :
    ¬ VolumeUniformQuotientPoincareGate d 2 Nc ρ := by
  rintro ⟨CP, hCP, hall⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (5 * CP)
  let M : ℕ := n + 1
  letI : NeZero M := ⟨by simp [M]⟩
  have hMgt : 5 * CP < (M : ℝ) := by
    dsimp [M]
    exact hn.trans (by norm_num)
  let i : Fin d := ⟨0, by omega⟩
  let j : Fin d := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have := congrArg Fin.val h
    simp [i, j] at this
  have hdim : 0 < Nc ^ 2 - 1 := by
    have h4 : 2 * 2 ≤ Nc * Nc := Nat.mul_le_mul hNc hNc
    have hsq : Nc ^ 2 = Nc * Nc := by ring
    omega
  let w : SUNLieCoord Nc := EuclideanSpace.single ⟨0, hdim⟩ (1 : ℝ)
  have hw : w ≠ 0 := by
    intro h0
    have hnorm : ‖w‖ = 1 := by
      simp [w, EuclideanSpace.norm_single]
    rw [h0, norm_zero] at hnorm
    norm_num at hnorm
  have hP : QuotientFlatGaugeHodgePoincare d M 2 Nc ρ CP := by
    simpa [M] using hall n
  let A := squareModeFine d M Nc i j w
  have hfluct : IsFluctuationCochain A :=
    squareModeFine_isFluctuation d M Nc i j w
  have hPoincare := hP.2 A hfluct
  have htotal := squareMode_mul_totalEnergy_le_five_norm_sq
    d M Nc hd ρ i j hij w
  have hnormpos : 0 < ‖A‖ ^ 2 := by
    rw [show ‖A‖ ^ 2 = (((M * 2 : ℕ) : ℝ) ^ d * ‖w‖ ^ 2) by
      exact norm_sq_squareModeFine d M Nc i j w]
    have hside : (0 : ℝ) < ((M * 2 : ℕ) : ℝ) := by positivity
    have hwpos : (0 : ℝ) < ‖w‖ ^ 2 := by
      have : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
      positivity
    exact mul_pos (pow_pos hside d) hwpos
  have hmul := mul_le_mul_of_nonneg_left hPoincare (Nat.cast_nonneg M)
  have hmul' :
      (M : ℝ) * ‖A‖ ^ 2 ≤
        CP * ((M : ℝ) *
          (inner ℝ A (flatGaugeHodgeK0CLM d (M * 2) Nc ρ A) +
            ‖flatBlockConstraintQCLM (d := d) (Nc := Nc) M 2 A‖ ^ 2)) := by
    calc
      (M : ℝ) * ‖A‖ ^ 2 ≤
          (M : ℝ) * (CP *
            (inner ℝ A (flatGaugeHodgeK0CLM d (M * 2) Nc ρ A) +
              ‖flatBlockConstraintQCLM (d := d) (Nc := Nc) M 2 A‖ ^ 2)) := hmul
      _ = _ := by ring
  have hupper := mul_le_mul_of_nonneg_left htotal hCP.le
  have hfinal : (M : ℝ) * ‖A‖ ^ 2 ≤ 5 * CP * ‖A‖ ^ 2 := by
    calc
      (M : ℝ) * ‖A‖ ^ 2 ≤ CP * ((M : ℝ) *
          (inner ℝ A (flatGaugeHodgeK0CLM d (M * 2) Nc ρ A) +
            ‖flatBlockConstraintQCLM (d := d) (Nc := Nc) M 2 A‖ ^ 2)) := hmul'
      _ ≤ CP * (5 * ‖A‖ ^ 2) := hupper
      _ = 5 * CP * ‖A‖ ^ 2 := by ring
  nlinarith

end YangMills.RG
