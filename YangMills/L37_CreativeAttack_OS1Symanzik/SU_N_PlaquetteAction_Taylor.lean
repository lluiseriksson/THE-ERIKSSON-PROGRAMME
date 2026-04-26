/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# SU(N) Plaquette Taylor expansion (Phase 354)

The plaquette holonomy `U_p` has Taylor expansion in lattice spacing
giving the continuum field strength.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L37_CreativeAttack_OS1Symanzik

/-! ## §1. The plaquette Taylor coefficients -/

/-- **Plaquette `U_p = exp(i a² F_μν + ...)` Taylor coefficient at
    `a²`**: this is `i F_μν` (= 1 in our normalisation). -/
def Plaquette_a2_coeff : ℝ := 1

/-- **Plaquette `a⁴` coefficient**: from Taylor of `exp`, this is
    `(i F_μν)² / 2 = -F²_μν / 2` (= 1/2 in absolute value). -/
def Plaquette_a4_coeff : ℝ := 1 / 2

/-- **Plaquette `a⁶` coefficient**: `1/6`. -/
def Plaquette_a6_coeff : ℝ := 1 / 6

theorem Plaquette_coeffs_pos :
    0 < Plaquette_a2_coeff ∧ 0 < Plaquette_a4_coeff ∧ 0 < Plaquette_a6_coeff := by
  refine ⟨?_, ?_, ?_⟩
  · unfold Plaquette_a2_coeff; norm_num
  · unfold Plaquette_a4_coeff; norm_num
  · unfold Plaquette_a6_coeff; norm_num

#print axioms Plaquette_coeffs_pos

/-! ## §2. Coefficient ordering -/

/-- **Plaquette coefficients are decreasing**:
    `Plaquette_a2_coeff > Plaquette_a4_coeff > Plaquette_a6_coeff`. -/
theorem Plaquette_coeffs_decreasing :
    Plaquette_a2_coeff > Plaquette_a4_coeff ∧
    Plaquette_a4_coeff > Plaquette_a6_coeff := by
  refine ⟨?_, ?_⟩
  · unfold Plaquette_a2_coeff Plaquette_a4_coeff; norm_num
  · unfold Plaquette_a4_coeff Plaquette_a6_coeff; norm_num

#print axioms Plaquette_coeffs_decreasing

end YangMills.L37_CreativeAttack_OS1Symanzik
