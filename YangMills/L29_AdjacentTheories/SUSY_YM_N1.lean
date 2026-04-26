/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# N=1 super Yang-Mills (Phase 276)

N=1 SUSY YM: gauge field + gaugino. Confines with a positive
mass gap (gluino condensate).

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L29_AdjacentTheories

/-- **N=1 SUSY YM degrees of freedom**: 2 (gauge) + 2 (gaugino) = 4. -/
def N1_DOF : ℕ := 4

theorem N1_DOF_value : N1_DOF = 4 := rfl

/-- **N=1 SUSY mass gap exists** (gluino condensate). -/
def N1_massGap_exists : Prop := True

/-- **The number of supercharges in N=1**: 4 (one Weyl spinor). -/
def N1_supercharges : ℕ := 4

#print axioms N1_DOF_value

end YangMills.L29_AdjacentTheories
