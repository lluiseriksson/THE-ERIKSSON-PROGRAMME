import YangMills.RG.PhysicalGaugeCochains

/-!
# Constant-sector flat block control

This module records the exact norm bookkeeping for direction-wise constant
physical one-cochains under the current unscaled full-periodic block map.  It
does not prove the full periodic curl/divergence/block Poincare theorem.
-/

namespace YangMills.RG

open scoped BigOperators RealInnerProductSpace

/-- Norm squared of a direction-wise constant physical one-cochain. -/
theorem norm_sq_constantPhysicalGaugeOneCochain {d N Nc : ℕ} [NeZero N]
    (v : Fin d → SUNLieCoord Nc) :
    ‖constantPhysicalGaugeOneCochain
        (d := d) (N := N) (Nc := Nc) v‖ ^ 2
      = (N : ℝ) ^ d * ∑ i : Fin d, ‖v i‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [constantPhysicalGaugeOneCochain_apply]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [Finset.sum_const, Finset.card_univ, card_finBox]
  simp [nsmul_eq_mul, Finset.mul_sum]

/-- Exact norm squared of the flat block constraint on direction-wise constants.

The current `linAvg` normalization sends constants to `L` times constants, so
the coarse norm is `(L : ℝ)^2 * (N' : ℝ)^d` times the directional norm sum. -/
theorem flatBlockConstraintQCLM_constant_norm_sq {d L N' Nc : ℕ}
    [NeZero L] [NeZero N'] [NeZero Nc]
    (v : Fin d → SUNLieCoord Nc) :
    ‖flatBlockConstraintQCLM
        (d := d) (Nc := Nc) L N'
        (constantPhysicalGaugeOneCochain
          (d := d) (N := L * N') (Nc := Nc) v)‖ ^ 2
      = (L : ℝ) ^ 2 * (N' : ℝ) ^ d
          * ∑ i : Fin d, ‖v i‖ ^ 2 := by
  rw [flatBlockConstraintQCLM_constant]
  rw [norm_smul]
  rw [mul_pow]
  rw [norm_sq_constantPhysicalGaugeOneCochain]
  have hLnonneg : 0 ≤ (L : ℝ) := by
    exact_mod_cast Nat.zero_le L
  rw [Real.norm_of_nonneg hLnonneg]
  ring

/-- Exact constant-sector block control for the current full-periodic
normalization.

For constants on the fine side length `L * N'`, the fine norm squared is
`(L^d / L^2)` times the coarse block norm squared.  This is the sharp harmonic
sector normalization used by the future full Poincare theorem. -/
theorem flatBlockConstraint_controls_constantSector {d L N' Nc : ℕ}
    [NeZero L] [NeZero N'] [NeZero Nc]
    (v : Fin d → SUNLieCoord Nc) :
    ‖constantPhysicalGaugeOneCochain
        (d := d) (N := L * N') (Nc := Nc) v‖ ^ 2
      = ((L : ℝ) ^ d / (L : ℝ) ^ 2) *
          ‖flatBlockConstraintQCLM
              (d := d) (Nc := Nc) L N'
              (constantPhysicalGaugeOneCochain
                (d := d) (N := L * N') (Nc := Nc) v)‖ ^ 2 := by
  rw [norm_sq_constantPhysicalGaugeOneCochain]
  rw [flatBlockConstraintQCLM_constant_norm_sq]
  have hL : (L : ℝ) ≠ 0 := by
    exact_mod_cast NeZero.ne L
  field_simp [hL]
  rw [Nat.cast_mul, mul_pow]
  ring

end YangMills.RG
