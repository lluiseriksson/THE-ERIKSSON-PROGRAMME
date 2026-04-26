/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L39_CreativeAttack_BalabanRGTransfer.LSI_to_DLR_LSI

/-!
# SU(N) LSI application (Phase 378)

Application to SU(N) Wilson Gibbs measures.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L39_CreativeAttack_BalabanRGTransfer

/-! ## §1. SU(N) bulk LSI -/

/-- **SU(N) bulk LSI constant**: `c_SU_N := 1/N²` (placeholder
    decreasing in N). -/
def SU_N_bulk_LSI (N : ℕ) (hN : 1 ≤ N) : LSI :=
  { c := 1 / (N : ℝ) ^ 2
    c_pos := by
      have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN
      positivity }

/-! ## §2. SU(N) DLR-LSI via transfer -/

/-- **SU(N) DLR-LSI**: derived from bulk LSI + default transfer. -/
def SU_N_DLR_LSI (N : ℕ) (hN : 1 ≤ N) : DLR_LSI :=
  LSI_implies_DLR_LSI (SU_N_bulk_LSI N hN) defaultTransfer

/-- **SU(N) DLR-LSI constant equals bulk LSI constant** (default
    transfer). -/
theorem SU_N_DLR_LSI_constant (N : ℕ) (hN : 1 ≤ N) :
    (SU_N_DLR_LSI N hN).c_DLR = (SU_N_bulk_LSI N hN).c :=
  tight_transfer _

#print axioms SU_N_DLR_LSI_constant

/-! ## §3. SU(2) and SU(3) instances -/

/-- **SU(2) DLR-LSI constant = 1/4**. -/
theorem SU2_DLR_LSI_constant :
    (SU_N_DLR_LSI 2 (by omega)).c_DLR = 1/4 := by
  rw [SU_N_DLR_LSI_constant]
  unfold SU_N_bulk_LSI
  simp; norm_num

/-- **SU(3) DLR-LSI constant = 1/9**. -/
theorem SU3_DLR_LSI_constant :
    (SU_N_DLR_LSI 3 (by omega)).c_DLR = 1/9 := by
  rw [SU_N_DLR_LSI_constant]
  unfold SU_N_bulk_LSI
  simp; norm_num

#print axioms SU3_DLR_LSI_constant

end YangMills.L39_CreativeAttack_BalabanRGTransfer
