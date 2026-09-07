/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP109PhysicalConstraintRightInverse
import YangMills.RG.BalabanCMP96ConstraintElimination

/-!
# Pivot support of the physical CMP109 constraint right inverse

The physical right-inverse candidate is obtained by solving the coarse pivot
response and then applying the literal sparse insertion of CMP96.  Independently
of the still-open block-diagonality of that coarse inverse, its fine field is
therefore supported exactly on the distinguished pivot bonds.

This module exposes the two pointwise facts needed by the source dictionary:

* away from the image of `b₀`, the inserted field is zero;
* at `b₀(c)`, its value is the exact `L^(d-1)`-scaled value of the solved
  coarse field at `c`.

The second statement does **not** claim that the solved value at `c` depends
only on the input at `c`.  That source-local dependence remains the
block-diagonality obligation for the physical pivot response.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d L N' Nc : ℕ}
variable [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
  [NeZero (L * N')]

/-- The constructed physical right inverse vanishes away from the literal
source pivot bonds. -/
theorem cmp109PhysicalConstraintRightInverseCLM_apply_eq_zero_of_not_pivot
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (D : CoarsePhysicalOneCochain d N' Nc)
    (p : PhysicalBond d (L * N'))
    (hp : ∀ c : PhysicalBond d N',
      p ≠ cmp96ConstraintPivotBond (d := d) (L := L) (N' := N') c) :
    cmp109PhysicalConstraintRightInverseCLM U D p = 0 := by
  rw [cmp109PhysicalConstraintRightInverseCLM_apply]
  exact cmp96ConstraintPivotInsertion_apply_of_not_pivot
    (cmp109PhysicalPivotInverseCLM U D) p hp

/-- Evaluation on `b₀(c)` exposes the exact solved coarse coefficient. -/
theorem cmp109PhysicalConstraintRightInverseCLM_apply_pivot
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (D : CoarsePhysicalOneCochain d N' Nc)
    (c : PhysicalBond d N') :
    cmp109PhysicalConstraintRightInverseCLM U D
        (cmp96ConstraintPivotBond (d := d) (L := L) (N' := N') c) =
      ((L : ℝ) ^ (d - 1)) •
        (cmp109PhysicalPivotInverseCLM U D) c := by
  rw [cmp109PhysicalConstraintRightInverseCLM_apply]
  exact cmp96ConstraintPivotInsertion_apply_pivot
    (cmp109PhysicalPivotInverseCLM U D) c

end

end YangMills.RG
