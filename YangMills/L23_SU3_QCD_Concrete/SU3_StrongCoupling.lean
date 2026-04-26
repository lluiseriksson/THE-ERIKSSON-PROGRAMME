/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# SU(3) strong coupling expansion (Phase 218)

## Strategic placement

This is **Phase 218** of the L23_SU3_QCD_Concrete block.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L23_SU3_QCD_Concrete

/-- **Strong coupling expansion** for SU(3). -/
structure StrongCouplingExpansion where
  c : ℕ → ℝ
  radius : ℝ
  radius_pos : 0 < radius

/-- **Truncated evaluation**. -/
def StrongCouplingExpansion.evalTruncated
    (sc : StrongCouplingExpansion) (n : ℕ) (β : ℝ) : ℝ :=
  (Finset.range n).sum (fun k => sc.c k * β ^ k)

/-- **At zero coupling, only `c 0` contributes**. -/
theorem StrongCouplingExpansion.evalTruncated_at_zero
    (sc : StrongCouplingExpansion) (n : ℕ) (h : 0 < n) :
    sc.evalTruncated n 0 = sc.c 0 := by
  unfold StrongCouplingExpansion.evalTruncated
  rw [show n = (n - 1) + 1 from (Nat.sub_add_cancel h).symm]
  rw [Finset.sum_range_succ']
  simp [pow_succ]

#print axioms StrongCouplingExpansion.evalTruncated_at_zero

end YangMills.L23_SU3_QCD_Concrete
