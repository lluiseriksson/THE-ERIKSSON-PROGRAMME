/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalGaugeFlatPoincare

/-!
# Critical block normalization in four dimensions

The existing volume-uniform Poincare wall is tied to the unscaled line-integral
block map.  This module keeps a scalar normalization `s` explicit and proves
the exact constant-sector scaling law.  In physical dimension four, every
scaled flat Hodge/block-Poincare estimate must satisfy

`L^2 ≤ CP * ‖s‖^2`.

Consequently the unscaled choice `s = 1` forces `CP` to grow at least like
`L^2`, while the critical RG choice `s = L` is exactly isometric on the
constant sector and leaves only the scale-independent necessary condition
`1 ≤ CP`.

This removes the *constant-sector obstruction* for the critically rescaled
gate.  It does not prove the full gate: fluctuation modes still require an
all-mode Poincare estimate or an interacting-Hessian argument.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

open Matrix Module
open scoped RealInnerProductSpace

/-- The physical block constraint with an explicit real normalization. -/
noncomputable def scaledFlatBlockConstraintQCLM
    {d L N' Nc : ℕ} [NeZero L] [NeZero N']
    (s : ℝ) :
    FinePhysicalOneCochain d L N' Nc →L[ℝ]
      CoarsePhysicalOneCochain d N' Nc :=
  s • flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'

@[simp]
theorem scaledFlatBlockConstraintQCLM_apply
    {d L N' Nc : ℕ} [NeZero L] [NeZero N']
    (s : ℝ) (A : FinePhysicalOneCochain d L N' Nc)
    (b : PhysicalBond d N') :
    scaledFlatBlockConstraintQCLM (d := d) (Nc := Nc) s A b =
      s • flatBlockConstraintQCLM (d := d) (Nc := Nc) L N' A b := by
  rfl

/-- A scaled block constraint sends a constant field to `s L` times the
corresponding coarse constant field. -/
theorem scaledFlatBlockConstraintQCLM_constant
    {d L N' Nc : ℕ} [NeZero L] [NeZero N'] [NeZero Nc]
    (s : ℝ) (v : Fin d → SUNLieCoord Nc) :
    scaledFlatBlockConstraintQCLM (d := d) (Nc := Nc) s
        (constantPhysicalGaugeOneCochain
          (d := d) (N := L * N') (Nc := Nc) v) =
      (s * (L : ℝ)) •
        constantPhysicalGaugeOneCochain
          (d := d) (N := N') (Nc := Nc) v := by
  rw [scaledFlatBlockConstraintQCLM]
  rw [ContinuousLinearMap.smul_apply,
    flatBlockConstraintQCLM_constant, smul_smul]

/-- Exact squared norm of the scaled block constraint on constants. -/
theorem scaledFlatBlockConstraintQCLM_constant_norm_sq
    {d L N' Nc : ℕ} [NeZero L] [NeZero N'] [NeZero Nc]
    (s : ℝ) (v : Fin d → SUNLieCoord Nc) :
    ‖scaledFlatBlockConstraintQCLM (d := d) (Nc := Nc) s
        (constantPhysicalGaugeOneCochain
          (d := d) (N := L * N') (Nc := Nc) v)‖ ^ 2 =
      ‖s‖ ^ 2 * (L : ℝ) ^ 2 * (N' : ℝ) ^ d
        * ∑ i : Fin d, ‖v i‖ ^ 2 := by
  rw [scaledFlatBlockConstraintQCLM]
  rw [ContinuousLinearMap.smul_apply, norm_smul]
  calc
    (‖s‖ * ‖flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
        (constantPhysicalGaugeOneCochain
          (d := d) (N := L * N') (Nc := Nc) v)‖) ^ 2 =
        ‖s‖ ^ 2 *
          ‖flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
            (constantPhysicalGaugeOneCochain
              (d := d) (N := L * N') (Nc := Nc) v)‖ ^ 2 := by ring
    _ = ‖s‖ ^ 2 * (L : ℝ) ^ 2 * (N' : ℝ) ^ d
        * ∑ i : Fin d, ‖v i‖ ^ 2 := by
          rw [flatBlockConstraintQCLM_constant_norm_sq]
          ring

/-- Flat Hodge/block-Poincare estimate with an explicit block normalization. -/
def ScaledFlatGaugeHodgePoincare
    (d L N' Nc : ℕ)
    [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (s CP : ℝ) : Prop :=
  0 < CP ∧
    ∀ A : FinePhysicalOneCochain d L N' Nc,
      ‖A‖ ^ 2 ≤
        CP *
          (inner ℝ A (flatGaugeHodgeK0CLM d (L * N') Nc ρ A)
            + ‖scaledFlatBlockConstraintQCLM
                (d := d) (Nc := Nc) s A‖ ^ 2)

/-- Exact necessary scaling law forced by any nonzero constant sector. -/
theorem scaledFlatGaugeHodgePoincare_constantSector_lower_bound
    {d L N' Nc : ℕ}
    [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) {s CP : ℝ}
    (hP : ScaledFlatGaugeHodgePoincare d L N' Nc ρ s CP)
    (v : Fin d → SUNLieCoord Nc)
    (hv : 0 < ∑ i : Fin d, ‖v i‖ ^ 2) :
    (L : ℝ) ^ d ≤ CP * ‖s‖ ^ 2 * (L : ℝ) ^ 2 := by
  let A : FinePhysicalOneCochain d L N' Nc :=
    constantPhysicalGaugeOneCochain
      (d := d) (N := L * N') (Nc := Nc) v
  have hK : flatGaugeHodgeK0CLM d (L * N') Nc ρ A = 0 := by
    dsimp [A]
    exact flatGaugeHodgeK0CLM_constantPhysicalGaugeOneCochain
      (d := d) (N := L * N') (Nc := Nc) ρ v
  have hmain := hP.2 A
  have hineq :
      ‖A‖ ^ 2 ≤ CP *
        ‖scaledFlatBlockConstraintQCLM (d := d) (Nc := Nc) s A‖ ^ 2 := by
    simpa [hK] using hmain
  let T : ℝ := (N' : ℝ) ^ d * ∑ i : Fin d, ‖v i‖ ^ 2
  have hNbase : (0 : ℝ) < (N' : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N')
  have hT : 0 < T := by
    dsimp [T]
    positivity
  have hfactored :
      (L : ℝ) ^ d * T ≤
        (CP * ‖s‖ ^ 2 * (L : ℝ) ^ 2) * T := by
    dsimp [A] at hineq
    rw [norm_sq_constantPhysicalGaugeOneCochain,
      scaledFlatBlockConstraintQCLM_constant_norm_sq] at hineq
    rw [Nat.cast_mul, mul_pow] at hineq
    convert hineq using 1 <;> dsimp [T] <;> ring
  exact (mul_le_mul_iff_of_pos_right hT).mp hfactored

/-- In dimension four the necessary scaling law is `L^2 ≤ CP ‖s‖^2`. -/
theorem scaledFlatGaugeHodgePoincare_four_necessary
    {L N' Nc : ℕ} [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) {s CP : ℝ}
    (hP : ScaledFlatGaugeHodgePoincare 4 L N' Nc ρ s CP)
    (v : Fin 4 → SUNLieCoord Nc)
    (hv : 0 < ∑ i : Fin 4, ‖v i‖ ^ 2) :
    (L : ℝ) ^ 2 ≤ CP * ‖s‖ ^ 2 := by
  have h := scaledFlatGaugeHodgePoincare_constantSector_lower_bound
    (d := 4) ρ hP v hv
  have hLbase : (0 : ℝ) < (L : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hL : (0 : ℝ) < (L : ℝ) ^ 2 := sq_pos_of_pos hLbase
  have hc :
      (L : ℝ) ^ 2 * (L : ℝ) ^ 2 ≤
        (CP * ‖s‖ ^ 2) * (L : ℝ) ^ 2 := by
    calc
      (L : ℝ) ^ 2 * (L : ℝ) ^ 2 = (L : ℝ) ^ 4 := by ring
      _ ≤ CP * ‖s‖ ^ 2 * (L : ℝ) ^ 2 := h
      _ = (CP * ‖s‖ ^ 2) * (L : ℝ) ^ 2 := by ring
  exact (mul_le_mul_iff_of_pos_right hL).mp hc

/-- In four dimensions the critical normalization `s = L` is exactly
isometric on direction-wise constant fields. -/
theorem criticalRescaledFlatBlockConstraint_constant_isometry
    {L N' Nc : ℕ} [NeZero L] [NeZero N'] [NeZero Nc]
    (v : Fin 4 → SUNLieCoord Nc) :
    ‖scaledFlatBlockConstraintQCLM (d := 4) (Nc := Nc) (L : ℝ)
        (constantPhysicalGaugeOneCochain
          (d := 4) (N := L * N') (Nc := Nc) v)‖ ^ 2 =
      ‖constantPhysicalGaugeOneCochain
          (d := 4) (N := L * N') (Nc := Nc) v‖ ^ 2 := by
  rw [scaledFlatBlockConstraintQCLM_constant_norm_sq,
    norm_sq_constantPhysicalGaugeOneCochain]
  have hL : (0 : ℝ) ≤ (L : ℝ) := by positivity
  rw [Real.norm_of_nonneg hL, Nat.cast_mul, mul_pow]
  ring

/-- The constant sector forces only the scale-independent condition `1 ≤ CP`
under the critical four-dimensional normalization. -/
theorem criticalRescaledFlatGaugeHodgePoincare_constantSector_lower_bound
    {L N' Nc : ℕ} [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) {CP : ℝ}
    (hP : ScaledFlatGaugeHodgePoincare 4 L N' Nc ρ (L : ℝ) CP)
    (v : Fin 4 → SUNLieCoord Nc)
    (hv : 0 < ∑ i : Fin 4, ‖v i‖ ^ 2) :
    1 ≤ CP := by
  have h := scaledFlatGaugeHodgePoincare_four_necessary ρ hP v hv
  have hLbase : (0 : ℝ) < (L : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hL : (0 : ℝ) < (L : ℝ) ^ 2 := sq_pos_of_pos hLbase
  have hnorm : ‖(L : ℝ)‖ ^ 2 = (L : ℝ) ^ 2 := by
    rw [Real.norm_of_nonneg (by positivity)]
  rw [hnorm] at h
  nlinarith

/-- The critically rescaled, constant-before-volume gate in physical
dimension four.  This module proves that the old constant-sector witness is
compatible with this gate; it deliberately does not inhabit the gate. -/
def VolumeUniformCriticalRescaledFlatPoincareGate
    (N' Nc : ℕ) [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) : Prop :=
  ∃ CP : ℝ, 0 < CP ∧
    ∀ L : ℕ,
      ScaledFlatGaugeHodgePoincare
        4 (L + 1) N' Nc ρ ((L + 1 : ℕ) : ℝ) CP

end YangMills.RG
