/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib

/-!
# Approximate Ward complexes

This file contains a deliberately small algebraic interface for the useful
part of the supersymmetric-cancellation idea: cancel `Q`-exact contributions
under an expectation functional before applying norms.

It does **not** formalise a supersymmetric Yang--Mills theory.  The structure
only records a continuous linear operator `Q`, an expectation functional, and a
quantitative Ward-defect bound

`‖expect (Q F)‖ ≤ defect * ‖F‖`.

When a local activity decomposes as `H = Q B + R`, the exact part contributes
only through the defect, while the remainder is estimated directly.  Downstream
polymer/RG code can consume this without committing to a physical source of
the Ward identity.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.SUSY

/-- A quantitative Ward-complex interface.

`defect = 0` is the exact Ward case.  Positive `defect` models a regulator,
mass, lattice-spacing, or cutoff error. -/
structure ApproxWardComplex (A : Type*) [NormedAddCommGroup A] [NormedSpace ℂ A] where
  /-- The odd/Ward differential or cohomological operator. -/
  Q : A →L[ℂ] A
  /-- The expectation or local integration functional. -/
  expect : A →L[ℂ] ℂ
  /-- Quantitative failure of the exact Ward identity. -/
  defect : ℝ
  defect_nonneg : 0 ≤ defect
  /-- Approximate Ward identity: `Q`-exact terms are killed up to `defect`. -/
  ward_bound : ∀ F : A, ‖expect (Q F)‖ ≤ defect * ‖F‖

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]

/-- In the exact Ward case, `Q`-exact terms have zero expectation. -/
theorem expect_Q_eq_zero_of_defect_eq_zero (W : ApproxWardComplex A)
    (hdefect : W.defect = 0) (F : A) :
    W.expect (W.Q F) = 0 := by
  have h := W.ward_bound F
  rw [hdefect, zero_mul] at h
  exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))

/-- Exact Ward cancellation for a decomposition `H = QB + R`. -/
theorem expect_eq_expect_remainder_of_defect_eq_zero (W : ApproxWardComplex A)
    (hdefect : W.defect = 0) (H B R : A) (hdec : H = W.Q B + R) :
    W.expect H = W.expect R := by
  calc
    W.expect H = W.expect (W.Q B + R) := by rw [hdec]
    _ = W.expect (W.Q B) + W.expect R := by rw [map_add]
    _ = 0 + W.expect R := by rw [expect_Q_eq_zero_of_defect_eq_zero W hdefect B]
    _ = W.expect R := by rw [zero_add]

/-- Approximate Ward cancellation for a decomposition `H = QB + R`.

This is the basic "cancel first, norm afterwards" estimate. -/
theorem expect_decomposition_bound (W : ApproxWardComplex A)
    (H B R : A) (hdec : H = W.Q B + R) :
    ‖W.expect H‖ ≤ W.defect * ‖B‖ + ‖W.expect R‖ := by
  calc
    ‖W.expect H‖ = ‖W.expect (W.Q B + R)‖ := by rw [hdec]
    _ = ‖W.expect (W.Q B) + W.expect R‖ := by rw [map_add]
    _ ≤ ‖W.expect (W.Q B)‖ + ‖W.expect R‖ := norm_add_le _ _
    _ ≤ W.defect * ‖B‖ + ‖W.expect R‖ :=
      add_le_add (W.ward_bound B) (le_refl _)

/-- Pointwise polymer/family version of approximate Ward cancellation.

If every activity `H X` decomposes as `Q (B X) + R X`, and the primitive and
remainder obey the same profile `w X`, then the integrated activity obeys the
profile with amplitude `defect * Bamp + Ramp`. -/
theorem expect_decomposition_profile_bound (W : ApproxWardComplex A)
    {ι : Type*} (H B R : ι → A) (w : ι → ℝ) (Bamp Ramp : ℝ)
    (hdec : ∀ X, H X = W.Q (B X) + R X)
    (hB : ∀ X, ‖B X‖ ≤ Bamp * w X)
    (hR : ∀ X, ‖W.expect (R X)‖ ≤ Ramp * w X) :
    ∀ X, ‖W.expect (H X)‖ ≤ (W.defect * Bamp + Ramp) * w X := by
  intro X
  have hQB : W.defect * ‖B X‖ ≤ W.defect * (Bamp * w X) :=
    mul_le_mul_of_nonneg_left (hB X) W.defect_nonneg
  calc
    ‖W.expect (H X)‖ ≤ W.defect * ‖B X‖ + ‖W.expect (R X)‖ :=
      expect_decomposition_bound W (H X) (B X) (R X) (hdec X)
    _ ≤ W.defect * (Bamp * w X) + Ramp * w X :=
      add_le_add hQB (hR X)
    _ = (W.defect * Bamp + Ramp) * w X := by ring

/-- Exact Ward cancellation for a whole activity family. -/
theorem expect_profile_bound_of_exact_ward (W : ApproxWardComplex A)
    {ι : Type*} (H B R : ι → A) (w : ι → ℝ) (Ramp : ℝ)
    (hdefect : W.defect = 0)
    (hdec : ∀ X, H X = W.Q (B X) + R X)
    (hR : ∀ X, ‖W.expect (R X)‖ ≤ Ramp * w X) :
    ∀ X, ‖W.expect (H X)‖ ≤ Ramp * w X := by
  intro X
  rw [expect_eq_expect_remainder_of_defect_eq_zero W hdefect (H X) (B X) (R X) (hdec X)]
  exact hR X

end YangMills.SUSY
