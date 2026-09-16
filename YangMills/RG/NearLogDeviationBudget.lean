/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.MatrixDetExpSkewAdjoint

/-!
# Uniform deviation budgets for the principal logarithm

This file converts one physical near-identity estimate `‖D - 1‖ ≤ δ`
into both analytic premises consumed by the determinant-one no-winding
closure.  The only remaining scalar condition is explicit:

`Nc * (δ / (1 - δ)) < 2 * π`.

No bound on `nearLog` is supplied by the caller.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- A uniform deviation bound transports through the sharp linear Mercator
estimate.  This is the monotonicity step needed by the physical no-winding
budget. -/
theorem norm_nearLog_le_div_of_norm_le {Y : 𝔸} {δ : ℝ}
    (hδ : δ < 1) (hY : ‖Y‖ ≤ δ) :
    ‖nearLog Y‖ ≤ δ / (1 - δ) := by
  have hYlt : ‖Y‖ < 1 := lt_of_le_of_lt hY hδ
  have hdenY : 0 < 1 - ‖Y‖ := sub_pos.mpr hYlt
  have hdenδ : 0 < 1 - δ := sub_pos.mpr hδ
  calc
    ‖nearLog Y‖ ≤ ‖Y‖ / (1 - ‖Y‖) := norm_nearLog_le_linear hYlt
    _ ≤ δ / (1 - δ) := by
      apply (div_le_div_iff₀ hdenY hdenδ).2
      nlinarith [norm_nonneg Y]

/-- The complete scalar budget needed to exclude a nonzero determinant
winding number. -/
structure MatrixNearLogNoWindingBudget (Nc : ℕ) where
  /-- Uniform radius of the physical deviation ball. -/
  δ : ℝ
  /-- The deviation ball lies inside the Mercator radius. -/
  δ_lt_one : δ < 1
  /-- The induced logarithmic trace lies strictly below the first winding. -/
  noWinding : (Nc : ℝ) * (δ / (1 - δ)) < 2 * Real.pi

variable {Nc : ℕ} [NeZero Nc]

/-- A physical deviation estimate inside a no-winding budget is automatically
inside the Mercator ball. -/
theorem MatrixNearLogNoWindingBudget.nearIdentity
    (B : MatrixNearLogNoWindingBudget Nc)
    (D : Matrix (Fin Nc) (Fin Nc) ℂ)
    (hdev : ‖D - 1‖ ≤ B.δ) :
    ‖D - 1‖ < 1 :=
  lt_of_le_of_lt hdev B.δ_lt_one

/-- The same physical deviation estimate automatically supplies the analytic
no-winding inequality for the principal logarithm. -/
theorem MatrixNearLogNoWindingBudget.nearLog_noWinding
    (B : MatrixNearLogNoWindingBudget Nc)
    (D : Matrix (Fin Nc) (Fin Nc) ℂ)
    (hdev : ‖D - 1‖ ≤ B.δ) :
    (Nc : ℝ) * ‖nearLog (D - 1)‖ < 2 * Real.pi := by
  apply lt_of_le_of_lt _ B.noWinding
  exact mul_le_mul_of_nonneg_left
    (norm_nearLog_le_div_of_norm_le B.δ_lt_one hdev)
    (Nat.cast_nonneg Nc)

/-- **Physical deviation-budget no-winding closure.**  For a determinant-one
unitary, one uniform deviation estimate now produces the near-identity and
no-winding premises internally. -/
theorem trace_nearLog_unitary_sub_one_eq_zero_of_det_eq_one_of_deviationBudget
    (D : unitary (Matrix (Fin Nc) (Fin Nc) ℂ))
    (B : MatrixNearLogNoWindingBudget Nc)
    (hdev : ‖(D : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ B.δ)
    (hdet : Matrix.det (D : Matrix (Fin Nc) (Fin Nc) ℂ) = 1) :
    Matrix.trace
      (nearLog ((D : Matrix (Fin Nc) (Fin Nc) ℂ) - 1)) = 0 := by
  exact trace_nearLog_unitary_sub_one_eq_zero_of_det_eq_one_of_noWinding
    D (B.nearIdentity (D : Matrix (Fin Nc) (Fin Nc) ℂ) hdev) hdet
      (B.nearLog_noWinding (D : Matrix (Fin Nc) (Fin Nc) ℂ) hdev)

end

end YangMills.RG
