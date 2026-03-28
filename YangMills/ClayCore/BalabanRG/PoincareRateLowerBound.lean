import Mathlib
import YangMills.ClayCore.BalabanRG.PhysicalRGRates

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# PoincareRateLowerBound — Layer 8B

Target: discharge `cP_linear_lb` from `PhysicalRGRates`.
Source: P69 (Ricci=N/4 → single-scale Poincaré), P70 (uniform coercivity).

physicalPoincareConstant N_c β = (N_c/4) · β
cP_linear_lb_from_E26: LinearLowerBound (physicalPoincareConstant N_c)
  Witness: β₀ = 1, c = N_c/4. For β ≥ 1: N_c/4 ≤ (N_c/4)·β. QED.

Remaining: connect polymer Dirichlet Poincaré to physicalPoincareConstant.
  Requires: sun_bakry_emery_cd + bakry_emery_lsi (P8 axioms, Mathlib gap).
-/

noncomputable section

/-- Helper: NeZero N_c → 0 < (N_c : ℝ) -/
theorem Nc_pos (N_c : ℕ) [NeZero N_c] : 0 < (N_c : ℝ) :=
  Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N_c))

/-- The physical Poincaré constant: cP(β) = (N_c/4) · β. -/
def physicalPoincareConstant (N_c : ℕ) [NeZero N_c] (β : ℝ) : ℝ :=
  (N_c : ℝ) / 4 * β

/-- (N_c/4) > 0 -/
private theorem coef_pos (N_c : ℕ) [NeZero N_c] : 0 < (N_c : ℝ) / 4 :=
  div_pos (Nc_pos N_c) (by norm_num)

/-- cP(β) > 0 for β > 0. -/
theorem physicalPoincareConstant_pos (N_c : ℕ) [NeZero N_c]
    (β : ℝ) (hβ : 0 < β) : 0 < physicalPoincareConstant N_c β :=
  mul_pos (coef_pos N_c) hβ

/-- cP is monotone. -/
theorem physicalPoincareConstant_monotone (N_c : ℕ) [NeZero N_c]
    (β₀ β : ℝ) (hβ : β₀ ≤ β) :
    physicalPoincareConstant N_c β₀ ≤ physicalPoincareConstant N_c β :=
  mul_le_mul_of_nonneg_left hβ (coef_pos N_c).le

/-- LinearLowerBound for physicalPoincareConstant.
    Witness β₀ = 1, c = N_c/4.  For β ≥ 1: N_c/4 = (N_c/4)·1 ≤ (N_c/4)·β. -/
theorem cP_linear_lb_from_E26 (_d N_c : ℕ) [NeZero N_c] :
    LinearLowerBound (physicalPoincareConstant N_c) := by
  refine ⟨1, (N_c : ℝ) / 4, one_pos, coef_pos N_c, fun β hβ => ?_⟩
  show (N_c : ℝ) / 4 ≤ physicalPoincareConstant N_c β
  unfold physicalPoincareConstant
  calc (N_c : ℝ) / 4 = (N_c : ℝ) / 4 * 1   := (mul_one _).symm
    _ ≤ (N_c : ℝ) / 4 * β                   :=
        mul_le_mul_of_nonneg_left hβ (coef_pos N_c).le

end

end YangMills.ClayCore
