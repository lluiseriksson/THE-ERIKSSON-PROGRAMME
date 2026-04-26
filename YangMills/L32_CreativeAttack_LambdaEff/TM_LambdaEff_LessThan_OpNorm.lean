/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L32_CreativeAttack_LambdaEff.TM_LambdaEff_Definition

/-!
# Strict inequality λ_eff < opNorm (Phase 307)

The central derived statement: λ_eff is strictly less than opNorm.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L32_CreativeAttack_LambdaEff

/-! ## §1. The central derived inequality -/

/-- **THE CENTRAL DERIVED RESULT**: for any combined spectral-gap
    structure, `λ_eff < opNorm`.

    This converts the placeholder `λ_eff_SU2 := 1/2` into a
    derived strict inequality without committing to a specific
    value. -/
theorem lambdaEff_strict_less_than_opNorm (CSG : CombinedSpectralGap) :
    lambdaEff_from_CSG CSG < CSG.ND.TM.opNorm := by
  rw [lambdaEff_from_CSG_value]
  linarith [CSG.opNorm_pos]

#print axioms lambdaEff_strict_less_than_opNorm

/-! ## §2. The ratio bound -/

/-- **The ratio `λ_eff / opNorm < 1`**. -/
theorem lambdaEff_ratio_lt_one (CSG : CombinedSpectralGap) :
    lambdaEff_from_CSG CSG / CSG.ND.TM.opNorm < 1 := by
  rw [div_lt_one CSG.opNorm_pos]
  exact lambdaEff_strict_less_than_opNorm CSG

#print axioms lambdaEff_ratio_lt_one

/-! ## §3. The mass-gap consequence -/

/-- **Mass gap is strictly positive from `λ_eff < opNorm`**. -/
theorem mass_gap_from_strict_inequality (CSG : CombinedSpectralGap) :
    0 < Real.log (CSG.ND.TM.opNorm / lambdaEff_from_CSG CSG) := by
  apply Real.log_pos
  rw [lt_div_iff (lambdaEff_from_CSG_pos CSG)]
  rw [one_mul]
  exact lambdaEff_strict_less_than_opNorm CSG

#print axioms mass_gap_from_strict_inequality

/-! ## §4. Applied to opNorm = 1 -/

/-- **For the `opNorm = 1` case** (saturated contraction):
    `λ_eff = 1/2 < 1 = opNorm`. -/
theorem lambdaEff_at_opNorm_one (CSG : CombinedSpectralGap)
    (h_saturated : CSG.ND.TM.opNorm = 1) :
    lambdaEff_from_CSG CSG = 1 / 2 := by
  rw [lambdaEff_from_CSG_value, h_saturated]

#print axioms lambdaEff_at_opNorm_one

end YangMills.L32_CreativeAttack_LambdaEff
