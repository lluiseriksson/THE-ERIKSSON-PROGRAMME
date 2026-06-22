import YangMills.RG.PhysicalGaugeHodgePoincare

/-!
# Constant-sector flat block control and harmonic-kernel bridge

This module records the exact norm bookkeeping for direction-wise constant
physical one-cochains under the current unscaled full-periodic block map.  It
does not prove the full periodic curl/divergence/block Poincare theorem.
-/

namespace YangMills.RG

open scoped BigOperators RealInnerProductSpace

/-- Every flat harmonic physical one-cochain on the full periodic lattice is
direction-wise constant.

This predicate isolates the missing reverse implication only.  The forward
direction, namely that direction-wise constant fields are flat harmonic, is
already proved by `isFlatHarmonicOneCochain_constantPhysicalGaugeOneCochain`. -/
def FlatHarmonicKernelClassified
    (d N Nc : ℕ)
    [NeZero d] [NeZero N] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) : Prop :=
  ∀ A : PhysicalGaugeOneCochain d N Nc,
    IsFlatHarmonicOneCochain ρ A →
      ∃ v : Fin d → SUNLieCoord Nc,
        A =
          constantPhysicalGaugeOneCochain
            (d := d) (N := N) (Nc := Nc) v

/-- Under the classification bridge, flat harmonic one-cochains are exactly the
direction-wise constant sector. -/
theorem flatHarmonicKernel_eq_constantSector
    {d N Nc : ℕ}
    [NeZero d] [NeZero N] [NeZero Nc]
    (ρ : SUNAdjointModel Nc)
    (hclass : FlatHarmonicKernelClassified d N Nc ρ)
    (A : PhysicalGaugeOneCochain d N Nc) :
    IsFlatHarmonicOneCochain ρ A ↔
      ∃ v : Fin d → SUNLieCoord Nc,
        A =
          constantPhysicalGaugeOneCochain
            (d := d) (N := N) (Nc := Nc) v := by
  constructor
  · exact hclass A
  · rintro ⟨v, rfl⟩
    exact
      isFlatHarmonicOneCochain_constantPhysicalGaugeOneCochain
        (d := d) (N := N) (Nc := Nc) ρ v

/-- Operator-kernel form of `flatHarmonicKernel_eq_constantSector`. -/
theorem flatGaugeHodgeKernel_eq_constantSector
    {d N Nc : ℕ}
    [NeZero d] [NeZero N] [NeZero Nc]
    (ρ : SUNAdjointModel Nc)
    (hclass : FlatHarmonicKernelClassified d N Nc ρ)
    (A : PhysicalGaugeOneCochain d N Nc) :
    flatGaugeHodgeK0CLM d N Nc ρ A = 0 ↔
      ∃ v : Fin d → SUNLieCoord Nc,
        A =
          constantPhysicalGaugeOneCochain
            (d := d) (N := N) (Nc := Nc) v := by
  rw [flatGaugeHodgeK0CLM_eq_zero_iff_isFlatHarmonicOneCochain]
  exact flatHarmonicKernel_eq_constantSector ρ hclass A

/-- If the flat harmonic kernel is classified by direction-wise constants, then
the joint kernel of the flat Hodge operator and the unscaled block constraint is
trivial at each fixed volume. -/
theorem flatJointKernel_trivial_of_harmonicClassification
    {d L N' Nc : ℕ}
    [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc)
    (hclass :
      FlatHarmonicKernelClassified d (L * N') Nc ρ)
    (A : FinePhysicalOneCochain d L N' Nc) :
    (flatGaugeHodgeK0CLM d (L * N') Nc ρ A = 0 ∧
      flatBlockConstraintQCLM
        (d := d) (Nc := Nc) L N' A = 0) ↔
      A = 0 := by
  constructor
  · rintro ⟨hK, hQ⟩
    have hharm :
        IsFlatHarmonicOneCochain ρ A :=
      (flatGaugeHodgeK0CLM_eq_zero_iff_isFlatHarmonicOneCochain
        (d := d) (N := L * N') (Nc := Nc) ρ A).mp hK
    obtain ⟨v, rfl⟩ := hclass A hharm
    have hv : v = 0 :=
      (flatConstant_jointKernel_eq_zero_iff
        (d := d) (L := L) (N' := N') (Nc := Nc) ρ v).mp
        ⟨hK, hQ⟩
    subst v
    apply PiLp.ext
    intro b
    simp
  · rintro rfl
    simp

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
