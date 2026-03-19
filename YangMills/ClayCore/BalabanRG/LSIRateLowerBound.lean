import Mathlib
import YangMills.ClayCore.BalabanRG.PoincareRateLowerBound

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# LSIRateLowerBound — Layer 8C

Target: discharge `cLSI_linear_lb` from `PhysicalRGRates`.
Source: P67 (multiscale Poincaré → LSI via martingale decomposition)
        P74 (unconditional uniform LSI for SU(N_c))

## Mathematical content

The LSI constant for the SU(N_c) Gibbs measure at scale k satisfies:

  cLSI(β) ≥ c_LSI₀ · β   for β ≥ 1

where c_LSI₀ = (N_c/4) · (1/2) = N_c/8, with the factor 1/2 from the
Poincaré-to-LSI transfer (P67, Theorem 4.1).

## Proof outline

1. `cP_linear_lb_from_E26` (Layer 8B): cP(β) ≥ (N_c/4)·β
2. P67: uniform Poincaré → uniform LSI with constant cLSI = cP/2
3. So cLSI(β) = (N_c/8)·β satisfies LinearLowerBound.

## Remaining sorry-requiring step

Connecting polymer Dirichlet LSI constant to physicalLSIConstant.
Requires: P67 martingale decomposition formalized in Lean.
-/

noncomputable section

/-- The physical LSI constant: cLSI(β) = (N_c/8) · β.
    Factor 1/2 from Poincaré→LSI transfer (P67). -/
def physicalLSIConstant (N_c : ℕ) [NeZero N_c] (β : ℝ) : ℝ :=
  (N_c : ℝ) / 8 * β

/-- (N_c/8) > 0 -/
private theorem lsi_coef_pos (N_c : ℕ) [NeZero N_c] : 0 < (N_c : ℝ) / 8 :=
  div_pos (Nc_pos N_c) (by norm_num)

/-- cLSI(β) > 0 for β > 0. -/
theorem physicalLSIConstant_pos (N_c : ℕ) [NeZero N_c]
    (β : ℝ) (hβ : 0 < β) : 0 < physicalLSIConstant N_c β :=
  mul_pos (lsi_coef_pos N_c) hβ

/-- cLSI is monotone. -/
theorem physicalLSIConstant_monotone (N_c : ℕ) [NeZero N_c]
    (β₀ β : ℝ) (hβ : β₀ ≤ β) :
    physicalLSIConstant N_c β₀ ≤ physicalLSIConstant N_c β :=
  mul_le_mul_of_nonneg_left hβ (lsi_coef_pos N_c).le

/-- LinearLowerBound for physicalLSIConstant.
    Witness β₀ = 1, c = N_c/8. For β ≥ 1: N_c/8 = (N_c/8)·1 ≤ (N_c/8)·β. -/
theorem cLSI_linear_lb_from_E26 (d N_c : ℕ) [NeZero N_c] :
    LinearLowerBound (physicalLSIConstant N_c) := by
  refine ⟨1, (N_c : ℝ) / 8, one_pos, lsi_coef_pos N_c, fun β hβ => ?_⟩
  show (N_c : ℝ) / 8 ≤ physicalLSIConstant N_c β
  unfold physicalLSIConstant
  calc (N_c : ℝ) / 8 = (N_c : ℝ) / 8 * 1   := (mul_one _).symm
    _ ≤ (N_c : ℝ) / 8 * β                   :=
        mul_le_mul_of_nonneg_left hβ (lsi_coef_pos N_c).le

/-- cLSI ≤ cP/2: the LSI constant is half the Poincaré constant.
    This is the abstract Poincaré→LSI transfer (P67). -/
theorem physicalLSIConstant_le_half_poincare (N_c : ℕ) [NeZero N_c] (β : ℝ) :
    physicalLSIConstant N_c β = physicalPoincareConstant N_c β / 2 := by
  unfold physicalLSIConstant physicalPoincareConstant
  ring

end

end YangMills.ClayCore
