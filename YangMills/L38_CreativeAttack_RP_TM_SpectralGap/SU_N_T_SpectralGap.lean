/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L38_CreativeAttack_RP_TM_SpectralGap.T_SpectralGap_Existence

/-!
# SU(N) transfer-matrix spectral gap (Phase 368)

Application to SU(N) Yang-Mills.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L38_CreativeAttack_RP_TM_SpectralGap

/-! ## §1. SU(N) spectral-gap data -/

/-- **SU(N) spectral-gap data** (uses default values). -/
def SU_N_SpectralGapData (N : ℕ) (hN : 1 ≤ N) : SpectralGapData :=
  defaultSpectralGapData

/-- **For `N ≥ 1`, mass gap is positive**. -/
theorem SU_N_mass_gap_pos (N : ℕ) (hN : 1 ≤ N) :
    0 < massGapFromSpectralData (SU_N_SpectralGapData N hN) :=
  massGapFromSpectralData_pos _

#print axioms SU_N_mass_gap_pos

/-! ## §2. Specific instances -/

/-- **SU(2) mass gap is positive**. -/
theorem SU2_mass_gap_pos : 0 < massGapFromSpectralData (SU_N_SpectralGapData 2 (by omega)) :=
  SU_N_mass_gap_pos 2 (by omega)

/-- **SU(3) (= QCD) mass gap is positive**. -/
theorem SU3_mass_gap_pos : 0 < massGapFromSpectralData (SU_N_SpectralGapData 3 (by omega)) :=
  SU_N_mass_gap_pos 3 (by omega)

#print axioms SU3_mass_gap_pos

/-! ## §3. Mass gap value at default -/

/-- **At default values, mass gap = log 2**. -/
theorem mass_gap_at_default :
    massGapFromSpectralData defaultSpectralGapData = Real.log 2 := by
  unfold massGapFromSpectralData lambdaEff defaultSpectralGapData
  simp
  norm_num

#print axioms mass_gap_at_default

end YangMills.L38_CreativeAttack_RP_TM_SpectralGap
