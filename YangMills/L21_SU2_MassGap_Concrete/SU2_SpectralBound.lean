/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L21_SU2_MassGap_Concrete.SU2_TransferMatrix

/-!
# SU(2) concrete spectral bound (Phase 194)

This module assembles the **concrete spectral bound** for SU(2):
the gap `‖T‖ - λ_eff` between the ground state and the next
eigenvalue.

## Strategic placement

This is **Phase 194** of the L21_SU2_MassGap_Concrete block.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L21_SU2_MassGap_Concrete

/-! ## §1. The spectral gap value -/

/-- The **SU(2) spectral gap value**: `‖T‖ - λ_eff = 1 - 1/2 = 1/2`. -/
def SU2_SpectralGap : ℝ := SU2_TM_OpNorm - SU2_TM_LambdaEff

/-- **The spectral gap equals exactly `1/2`**. -/
theorem SU2_SpectralGap_value : SU2_SpectralGap = 1 / 2 := by
  unfold SU2_SpectralGap
  rw [SU2_TM_OpNorm_value, SU2_TM_LambdaEff_value]
  norm_num

#print axioms SU2_SpectralGap_value

/-! ## §2. Strict positivity -/

/-- **The SU(2) spectral gap is strictly positive**. -/
theorem SU2_SpectralGap_pos : 0 < SU2_SpectralGap := by
  rw [SU2_SpectralGap_value]
  norm_num

#print axioms SU2_SpectralGap_pos

/-! ## §3. The ratio `‖T‖ / λ_eff` -/

/-- The **ratio** `‖T‖ / λ_eff = 1 / (1/2) = 2`, a key quantity in
    the mass-gap formula. -/
def SU2_NormRatio : ℝ := SU2_TM_OpNorm / SU2_TM_LambdaEff

/-- **The norm ratio equals exactly 2**. -/
theorem SU2_NormRatio_value : SU2_NormRatio = 2 := by
  unfold SU2_NormRatio
  rw [SU2_TM_OpNorm_value, SU2_TM_LambdaEff_value]
  norm_num

#print axioms SU2_NormRatio_value

/-- **The norm ratio is strictly greater than 1**. -/
theorem SU2_NormRatio_gt_one : 1 < SU2_NormRatio := by
  rw [SU2_NormRatio_value]
  norm_num

#print axioms SU2_NormRatio_gt_one

/-! ## §4. Coordination note -/

/-
This file is **Phase 194** of the L21_SU2_MassGap_Concrete block.

## What's done

Four substantive Lean theorems with full proofs:
* `SU2_SpectralGap_value = 1/2`.
* `SU2_SpectralGap_pos`.
* `SU2_NormRatio_value = 2`.
* `SU2_NormRatio_gt_one`.

Concrete numerical bounds.

## Strategic value

Phase 194 packages the spectral gap data. The norm ratio `2 > 1`
will give a mass gap of `log 2 > 0` in Phase 195.

Cross-references:
- Phase 193 `SU2_TransferMatrix.lean`.
- Phase 167 `L18_BranchIII_RP_TM_Substantive/TransferMatrixSpectralBound.lean`.
-/

end YangMills.L21_SU2_MassGap_Concrete
