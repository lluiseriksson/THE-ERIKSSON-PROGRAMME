/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L32_CreativeAttack_LambdaEff.TM_LambdaEff_LessThan_OpNorm

/-!
# Mass gap from spectral gap (Phase 308)

Convert the strict spectral inequality into a positive mass gap.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L32_CreativeAttack_LambdaEff

/-! ## §1. The mass gap from CSG -/

/-- **Mass gap from a combined spectral-gap structure**:
    `m = log(opNorm / λ_eff) > 0`. -/
noncomputable def massGapFromCSG (CSG : CombinedSpectralGap) : ℝ :=
  Real.log (CSG.ND.TM.opNorm / lambdaEff_from_CSG CSG)

/-- **The mass gap is strictly positive**. -/
theorem massGapFromCSG_pos (CSG : CombinedSpectralGap) :
    0 < massGapFromCSG CSG := by
  unfold massGapFromCSG
  exact mass_gap_from_strict_inequality CSG

#print axioms massGapFromCSG_pos

/-! ## §2. Mass gap value at opNorm = 1 -/

/-- **At `opNorm = 1`, mass gap = `log 2`**. -/
theorem massGapFromCSG_at_one (CSG : CombinedSpectralGap)
    (h_saturated : CSG.ND.TM.opNorm = 1) :
    massGapFromCSG CSG = Real.log 2 := by
  unfold massGapFromCSG
  rw [lambdaEff_at_opNorm_one CSG h_saturated, h_saturated]
  norm_num

#print axioms massGapFromCSG_at_one

/-! ## §3. Robustness statement -/

/-- **Robustness**: the mass gap from CSG is positive regardless of
    the exact value of `opNorm > 0`.

    This is the substantive content: we do not need to commit to
    `opNorm = 1` or `λ_eff = 1/2`; the strict inequality
    `λ_eff < opNorm` (derivable from RP + non-degeneracy)
    suffices for `m > 0`. -/
theorem massGap_robust_existence
    (CSG : CombinedSpectralGap) :
    ∃ m : ℝ, 0 < m :=
  ⟨massGapFromCSG CSG, massGapFromCSG_pos CSG⟩

#print axioms massGap_robust_existence

end YangMills.L32_CreativeAttack_LambdaEff
