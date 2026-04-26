/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L32_CreativeAttack_LambdaEff.TM_SpectralGap_Existence

/-!
# λ_eff definition (Phase 306)

Definition of λ_eff as `opNorm - δ` for the spectral gap `δ`.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L32_CreativeAttack_LambdaEff

/-! ## §1. λ_eff from gap -/

/-- **`λ_eff := opNorm - δ`** for a spectral gap `δ > 0`. -/
def lambdaEffFromGap (opNorm δ : ℝ) : ℝ := opNorm - δ

/-- **`λ_eff < opNorm`** when `δ > 0`. -/
theorem lambdaEff_lt_opNorm (opNorm δ : ℝ) (hδ : 0 < δ) :
    lambdaEffFromGap opNorm δ < opNorm := by
  unfold lambdaEffFromGap
  linarith

#print axioms lambdaEff_lt_opNorm

/-- **`λ_eff ≥ 0`** when `δ ≤ opNorm`. -/
theorem lambdaEff_nonneg (opNorm δ : ℝ) (hδ_le : δ ≤ opNorm) :
    0 ≤ lambdaEffFromGap opNorm δ := by
  unfold lambdaEffFromGap
  linarith

#print axioms lambdaEff_nonneg

/-! ## §2. Concrete λ_eff for the half-norm gap -/

/-- **Concrete λ_eff = opNorm/2** when `δ = opNorm/2`. -/
theorem lambdaEff_at_halfNormGap (opNorm : ℝ) :
    lambdaEffFromGap opNorm (opNorm / 2) = opNorm / 2 := by
  unfold lambdaEffFromGap
  ring

#print axioms lambdaEff_at_halfNormGap

/-! ## §3. Combined: λ_eff for any combined structure -/

/-- **`λ_eff_from_CSG`**: for a combined structure with
    `δ = halfNormGap`, the resulting λ_eff is `opNorm/2`. -/
def lambdaEff_from_CSG (CSG : CombinedSpectralGap) : ℝ :=
  lambdaEffFromGap CSG.ND.TM.opNorm (halfNormGap CSG)

/-- **The combined λ_eff equals `opNorm/2`**. -/
theorem lambdaEff_from_CSG_value (CSG : CombinedSpectralGap) :
    lambdaEff_from_CSG CSG = CSG.ND.TM.opNorm / 2 := by
  unfold lambdaEff_from_CSG halfNormGap
  exact lambdaEff_at_halfNormGap _

#print axioms lambdaEff_from_CSG_value

/-! ## §4. λ_eff is positive when opNorm is positive -/

/-- **`λ_eff > 0`** for any combined structure. -/
theorem lambdaEff_from_CSG_pos (CSG : CombinedSpectralGap) :
    0 < lambdaEff_from_CSG CSG := by
  rw [lambdaEff_from_CSG_value]
  exact half_pos CSG.opNorm_pos

#print axioms lambdaEff_from_CSG_pos

end YangMills.L32_CreativeAttack_LambdaEff
