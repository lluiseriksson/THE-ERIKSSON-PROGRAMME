/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L37_CreativeAttack_OS1Symanzik.SU_N_TaylorBound
import YangMills.L37_CreativeAttack_OS1Symanzik.SU_N_PlaquetteAction_Taylor

/-!
# SU(N) first-order artifact (Phase 355)

The leading `O(a²)` artifact in the SU(N) Wilson plaquette action.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L37_CreativeAttack_OS1Symanzik

/-! ## §1. The first-order artifact -/

/-- **First-order artifact coefficient for SU(N)**: combines the
    plaquette Taylor coefficient and the SU(N) factor. -/
def SU_N_FirstArtifact (N : ℕ) : ℝ :=
  Plaquette_a4_coeff * SU_N_TaylorCoeff_4 N

/-- **The artifact equals `(1/2) · (N/12) = N/24`**. -/
theorem SU_N_FirstArtifact_value (N : ℕ) :
    SU_N_FirstArtifact N = (N : ℝ) / 24 := by
  unfold SU_N_FirstArtifact Plaquette_a4_coeff SU_N_TaylorCoeff_4
  ring

#print axioms SU_N_FirstArtifact_value

/-! ## §2. Concrete instances -/

/-- **SU(2): artifact = 2/24 = 1/12**. -/
theorem SU2_FirstArtifact :
    SU_N_FirstArtifact 2 = 1/12 := by
  rw [SU_N_FirstArtifact_value]; norm_num

/-- **SU(3) (= QCD): artifact = 3/24 = 1/8**. -/
theorem SU3_FirstArtifact :
    SU_N_FirstArtifact 3 = 1/8 := by
  rw [SU_N_FirstArtifact_value]; norm_num

#print axioms SU3_FirstArtifact

/-! ## §3. Positivity -/

/-- **First artifact is positive for `N ≥ 1`**. -/
theorem SU_N_FirstArtifact_pos (N : ℕ) (hN : 1 ≤ N) :
    0 < SU_N_FirstArtifact N := by
  rw [SU_N_FirstArtifact_value]
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN
  positivity

#print axioms SU_N_FirstArtifact_pos

end YangMills.L37_CreativeAttack_OS1Symanzik
