/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalCriticalRescalingFourierNoGoAllScales

/-!
# Fourier no-go for arbitrary coarse postconditioners

The scalar normalization in the original critical gate is not the essential
restriction.  Let `T` be any continuous linear endomorphism of the coarse
physical one-cochain space and replace the block penalty by `‖T (Q A)‖²`.
The transverse Fourier witness is already in the exact kernel of `Q`, hence
every such postconditioner also annihilates it.  The same quadratic lower
bound on every admissible Poincare constant and the same volume-uniform no-go
therefore hold for an arbitrary scale-dependent family of postconditioners.
-/

namespace YangMills.RG

open Matrix Module

/-- Flat Hodge/block-Poincare estimate after an arbitrary continuous linear
postconditioning of the coarse block variable. -/
def PostconditionedFlatGaugeHodgePoincare
    (d L N' Nc : ℕ)
    [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc)
    (T : CoarsePhysicalOneCochain d N' Nc →L[ℝ]
      CoarsePhysicalOneCochain d N' Nc)
    (CP : ℝ) : Prop :=
  0 < CP ∧
    ∀ A : FinePhysicalOneCochain d L N' Nc,
      ‖A‖ ^ 2 ≤
        CP *
          (inner ℝ A (flatGaugeHodgeK0CLM d (L * N') Nc ρ A)
            + ‖T (flatBlockConstraintQCLM
                (d := d) (Nc := Nc) L N' A)‖ ^ 2)

/-- The Fourier witness gives the same lower bound after every coarse
postconditioner, because it lies in the kernel before postconditioning. -/
theorem postconditionedFlatPoincare_fourier_lower_bound
    (L N' Nc : ℕ) [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (hL : 2 ≤ L) (hNc : 2 ≤ Nc)
    (T : CoarsePhysicalOneCochain 4 N' Nc →L[ℝ]
      CoarsePhysicalOneCochain 4 N' Nc)
    (CP : ℝ)
    (hP : PostconditionedFlatGaugeHodgePoincare
      4 L N' Nc ρ T CP) :
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
      flatBlockConstraintQCLM (d := 4) (Nc := Nc) L N' A = 0 := by
    dsimp [A]
    exact flatBlockConstraintQCLM_blockFourierMode_eq_zero
      hL hNc i j hij
  have hT :
      T (flatBlockConstraintQCLM (d := 4) (Nc := Nc) L N' A) = 0 := by
    rw [hQ, map_zero]
  have hmain := hP.2 A
  rw [hT, norm_zero, zero_pow (by norm_num), add_zero, hH, hnorm] at hmain
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

/-- The constant-before-volume gate for an arbitrary scale-dependent family
of coarse postconditioners. -/
def VolumeUniformPostconditionedFlatPoincareGate
    (N' Nc : ℕ) [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc)
    (T : ℕ → CoarsePhysicalOneCochain 4 N' Nc →L[ℝ]
      CoarsePhysicalOneCochain 4 N' Nc) : Prop :=
  ∃ CP : ℝ, 0 < CP ∧
    ∀ k : ℕ,
      PostconditionedFlatGaugeHodgePoincare
        4 (k + 1) N' Nc ρ (T k) CP

/-- **Postconditioned all-scales Fourier no-go.**  No scale-dependent family
of continuous linear operators acting after the block map can restore a
volume-uniform full-space Poincare constant. -/
theorem volumeUniformPostconditionedFlatPoincareGate_fourier_false
    {N' Nc : ℕ} [NeZero N'] [NeZero Nc]
    (hNc : 2 ≤ Nc) (ρ : SUNAdjointModel Nc)
    (T : ℕ → CoarsePhysicalOneCochain 4 N' Nc →L[ℝ]
      CoarsePhysicalOneCochain 4 N' Nc) :
    ¬ VolumeUniformPostconditionedFlatPoincareGate N' Nc ρ T := by
  rintro ⟨CP, hCP, hall⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (4 * Real.pi ^ 2 * CP)
  let L := n + 2
  have hL : 2 ≤ L := by simp [L]
  haveI : NeZero L := ⟨by omega⟩
  let k := L - 1
  have hk : k + 1 = L := by
    dsimp [k]
    omega
  have hP : PostconditionedFlatGaugeHodgePoincare
      4 L N' Nc ρ (T k) CP := by
    simpa only [hk] using hall k
  have hone : 1 ≤ CP * blockFourierEigenvalue L :=
    postconditionedFlatPoincare_fourier_lower_bound
      L N' Nc ρ hL hNc (T k) CP hP
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
      _ = 4 * Real.pi ^ 2 * CP := by
        field_simp
        ring
  have hnR : 4 * Real.pi ^ 2 * CP < (n : ℝ) := by exact_mod_cast hn
  have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hbig : 4 * Real.pi ^ 2 * CP < (L : ℝ) ^ 2 := by
    dsimp [L]
    push_cast
    nlinarith
  linarith

end YangMills.RG
