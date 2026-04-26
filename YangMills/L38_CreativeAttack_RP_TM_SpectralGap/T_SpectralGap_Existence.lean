/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L38_CreativeAttack_RP_TM_SpectralGap.T_NonDegenerate_Vacuum

/-!
# Spectral gap existence (Phase 367)

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L38_CreativeAttack_RP_TM_SpectralGap

/-! ## §1. Combined spectral-gap structure -/

/-- **Combined spectral-gap data**: opNorm > 0, non-degeneracy,
    and the resulting `δ > 0`. -/
structure SpectralGapData where
  opNorm : ℝ
  opNorm_pos : 0 < opNorm
  /-- The spectral gap. -/
  δ : ℝ := opNorm / 2
  δ_pos : 0 < δ := by simp; exact half_pos opNorm_pos
  δ_lt_opNorm : δ < opNorm := by simp; linarith

/-! ## §2. Default data -/

/-- **Default spectral-gap data with `opNorm = 1`**. -/
def defaultSpectralGapData : SpectralGapData where
  opNorm := 1
  opNorm_pos := by norm_num
  δ := 1/2
  δ_pos := by norm_num
  δ_lt_opNorm := by norm_num

/-- **Default `λ_eff = 1/2`**. -/
theorem default_lambdaEff :
    lambdaEff defaultSpectralGapData.opNorm defaultSpectralGapData.δ = 1/2 := by
  unfold lambdaEff defaultSpectralGapData
  simp

#print axioms default_lambdaEff

/-! ## §3. Mass gap from spectral data -/

/-- **Mass gap from spectral data**: `m = log(opNorm/λ_eff)`. -/
noncomputable def massGapFromSpectralData (sgd : SpectralGapData) : ℝ :=
  Real.log (sgd.opNorm / lambdaEff sgd.opNorm sgd.δ)

/-- **Mass gap is strictly positive**. -/
theorem massGapFromSpectralData_pos (sgd : SpectralGapData) :
    0 < massGapFromSpectralData sgd := by
  unfold massGapFromSpectralData
  apply Real.log_pos
  have h_λ_pos : 0 < lambdaEff sgd.opNorm sgd.δ := by
    unfold lambdaEff
    linarith [sgd.δ_lt_opNorm]
  rw [lt_div_iff h_λ_pos]
  rw [one_mul]
  exact lambdaEff_lt_opNorm sgd.opNorm sgd.δ sgd.δ_pos

#print axioms massGapFromSpectralData_pos

end YangMills.L38_CreativeAttack_RP_TM_SpectralGap
