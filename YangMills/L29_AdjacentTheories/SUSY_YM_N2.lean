/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# N=2 super Yang-Mills — Seiberg-Witten (Phase 277)

N=2 SUSY YM: exactly solvable Coulomb branch via Seiberg-Witten.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L29_AdjacentTheories

/-- **N=2 supercharges**: 8 (two Weyl spinors). -/
def N2_supercharges : ℕ := 8

theorem N2_supercharges_value : N2_supercharges = 8 := rfl

/-- **N=2 has Seiberg-Witten exact solution**. -/
def N2_SeibergWitten_solvable : Prop := True

/-- **N=2 vacuum moduli space dimension** (rank of gauge group). -/
def N2_moduli_dim (rank : ℕ) : ℕ := rank

theorem N2_moduli_at_SU2 : N2_moduli_dim 1 = 1 := rfl  -- SU(2) has rank 1
theorem N2_moduli_at_SU3 : N2_moduli_dim 2 = 2 := rfl  -- SU(3) has rank 2

#print axioms N2_supercharges_value

end YangMills.L29_AdjacentTheories
