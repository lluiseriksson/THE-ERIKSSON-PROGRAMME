/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalCriticalRescalingFourierHodge

/-!
# Fourier no-go at every block side

The transverse Fourier cochain has exact flat-Hodge Rayleigh quotient
`blockFourierEigenvalue L`, bounded by `(2π/L)²`.  It belongs to the kernel of
every scalar rescaling of the flat block map.  Consequently the existing
full-space, critically rescaled Poincare gate is false for each fixed positive
coarse side `N'`.
-/

namespace YangMills.RG

open Matrix Module

/-- Exact Rayleigh quotient of the Fourier witness. -/
theorem blockFourierMode_rayleigh_eq
    (d L N' Nc : ℕ) [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (hL : 2 ≤ L) (hNc : 2 ≤ Nc)
    (i j : Fin d) (hij : i ≠ j) :
    inner ℝ (blockFourierModeCochain d L N' Nc hNc i j)
        (flatGaugeHodgeK0CLM d (L * N') Nc ρ
          (blockFourierModeCochain d L N' Nc hNc i j)) /
      ‖blockFourierModeCochain d L N' Nc hNc i j‖ ^ 2 =
        blockFourierEigenvalue L := by
  rw [flatGaugeHodgeK0_inner_blockFourierModeCochain_of_ne
      d L N' Nc ρ hL hNc i j hij,
    norm_sq_blockFourierModeCochain]
  have hside : (0 : ℝ) < (((L * N' : ℕ) : ℝ) ^ d) := by
    have hLN : 0 < L * N' := Nat.mul_pos
      (Nat.pos_of_ne_zero (NeZero.ne L))
      (Nat.pos_of_ne_zero (NeZero.ne N'))
    positivity
  field_simp

/-- The Fourier witness bounds every admissible Poincare constant from below. -/
theorem criticalRescaledFlatPoincare_fourier_lower_bound
    (L N' Nc : ℕ) [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (hL : 2 ≤ L) (hNc : 2 ≤ Nc) (CP : ℝ)
    (hP : ScaledFlatGaugeHodgePoincare 4 L N' Nc ρ (L : ℝ) CP) :
    1 ≤ CP * blockFourierEigenvalue L := by
  let i : Fin 4 := ⟨0, by omega⟩
  let j : Fin 4 := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j]
  let A : FinePhysicalOneCochain 4 L N' Nc :=
    blockFourierModeCochain 4 L N' Nc hNc i j
  have hnorm : ‖A‖ ^ 2 = (((L * N' : ℕ) : ℝ) ^ 4) := by
    dsimp [A]
    exact norm_sq_blockFourierModeCochain 4 L N' Nc hNc i j
  have hH :
      inner ℝ A (flatGaugeHodgeK0CLM 4 (L * N') Nc ρ A) =
        (((L * N' : ℕ) : ℝ) ^ 4) * blockFourierEigenvalue L := by
    dsimp [A]
    exact flatGaugeHodgeK0_inner_blockFourierModeCochain_of_ne
      4 L N' Nc ρ hL hNc i j hij
  have hQ :
      scaledFlatBlockConstraintQCLM (d := 4) (Nc := Nc) (L : ℝ) A = 0 := by
    dsimp [A]
    exact criticalScaledBlockConstraintQCLM_blockFourierMode_eq_zero
      hL hNc i j hij
  have hmain := hP.2 A
  rw [hQ, norm_zero, zero_pow (by norm_num), add_zero, hH, hnorm] at hmain
  have hvol : (0 : ℝ) < (((L * N' : ℕ) : ℝ) ^ 4) := by
    have hLN : 0 < L * N' := Nat.mul_pos
      (Nat.pos_of_ne_zero (NeZero.ne L))
      (Nat.pos_of_ne_zero (NeZero.ne N'))
    positivity
  have hfactored :
      (1 : ℝ) * (((L * N' : ℕ) : ℝ) ^ 4) ≤
        (CP * blockFourierEigenvalue L) *
          (((L * N' : ℕ) : ℝ) ^ 4) := by
    convert hmain using 1 <;> ring
  exact (mul_le_mul_iff_of_pos_right hvol).mp hfactored

/-- **All-scales Fourier no-go.**  Here `N'` is any fixed positive coarse
side, while the quantified side `L` is the varying block/fine scale. -/
theorem volumeUniformCriticalRescaledFlatPoincareGate_fourier_false
    {N' Nc : ℕ} [NeZero N'] [NeZero Nc]
    (hNc : 2 ≤ Nc) (ρ : SUNAdjointModel Nc) :
    ¬ VolumeUniformCriticalRescaledFlatPoincareGate N' Nc ρ := by
  rintro ⟨CP, hCP, hall⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (4 * Real.pi ^ 2 * CP)
  let L := n + 2
  have hL : 2 ≤ L := by simp [L]
  haveI : NeZero L := ⟨by omega⟩
  let k := L - 1
  have hk : k + 1 = L := by
    dsimp [k]
    omega
  have hP : ScaledFlatGaugeHodgePoincare 4 L N' Nc ρ (L : ℝ) CP := by
    simpa only [hk] using hall k
  have hone : 1 ≤ CP * blockFourierEigenvalue L :=
    criticalRescaledFlatPoincare_fourier_lower_bound
      L N' Nc ρ hL hNc CP hP
  have hlambda : blockFourierEigenvalue L ≤ (2 * Real.pi / L) ^ 2 :=
    blockFourierEigenvalue_le L
  have hone' : 1 ≤ CP * (2 * Real.pi / (L : ℝ)) ^ 2 :=
    le_trans hone (mul_le_mul_of_nonneg_left hlambda (le_of_lt hCP))
  have hLR : (0 : ℝ) < (L : ℝ) := by positivity
  have hLRne : (L : ℝ) ≠ 0 := ne_of_gt hLR
  have hscaled := mul_le_mul_of_nonneg_right hone' (sq_nonneg (L : ℝ))
  have hupper : (L : ℝ) ^ 2 ≤ 4 * Real.pi ^ 2 * CP := by
    calc
      (L : ℝ) ^ 2 = 1 * (L : ℝ) ^ 2 := by ring
      _ ≤ (CP * (2 * Real.pi / (L : ℝ)) ^ 2) * (L : ℝ) ^ 2 := hscaled
      _ = 4 * Real.pi ^ 2 * CP := by field_simp; ring
  have hnR : 4 * Real.pi ^ 2 * CP < (n : ℝ) := by exact_mod_cast hn
  have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hbig : 4 * Real.pi ^ 2 * CP < (L : ℝ) ^ 2 := by
    dsimp [L]
    push_cast
    nlinarith
  linarith

end YangMills.RG
