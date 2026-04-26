/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L32_CreativeAttack_LambdaEff.TM_PositivePerronFrobenius

/-!
# Spectral gap existence (Phase 305)

Existence of a spectral gap from RP + non-degeneracy.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L32_CreativeAttack_LambdaEff

/-! ## §1. Combined spectral gap structure -/

/-- **Combined: TM + non-degeneracy + positive opNorm**. -/
structure CombinedSpectralGap where
  ND : NonDegenerateMaximum
  /-- The operator norm is positive. -/
  opNorm_pos : 0 < ND.TM.opNorm

/-! ## §2. Strict gap exists -/

/-- **A strict spectral gap exists for any combined structure**. -/
theorem combinedSpectralGap_exists (CSG : CombinedSpectralGap) :
    hasStrictSpectralGap CSG.ND :=
  hasStrictSpectralGap_witness CSG.ND CSG.opNorm_pos

#print axioms combinedSpectralGap_exists

/-! ## §3. Concrete witnesses -/

/-- **Witness: half the operator norm**. -/
def halfNormGap (CSG : CombinedSpectralGap) : ℝ :=
  CSG.ND.TM.opNorm / 2

/-- **`halfNormGap` is positive**. -/
theorem halfNormGap_pos (CSG : CombinedSpectralGap) :
    0 < halfNormGap CSG := by
  unfold halfNormGap
  exact half_pos CSG.opNorm_pos

/-- **`halfNormGap < opNorm`**. -/
theorem halfNormGap_lt_norm (CSG : CombinedSpectralGap) :
    halfNormGap CSG < CSG.ND.TM.opNorm := by
  unfold halfNormGap
  linarith [CSG.opNorm_pos]

#print axioms halfNormGap_lt_norm

end YangMills.L32_CreativeAttack_LambdaEff
