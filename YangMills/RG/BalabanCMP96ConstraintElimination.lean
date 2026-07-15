/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP96ConstraintRightInverse

/-!
# The physical constraint-elimination operator `C`

With `Q` the flat block constraint and `E` its distinguished-bond right
inverse, define

`C = I - E Q`.

This is the padded square realization of Bałaban's rectangular coordinate
map from free fine bonds to constrained fine fields.  It is honest about that
typing: on the full fine space it is a projection onto `ker Q`; its restriction
to fields vanishing on every pivot `b₀(c)` is the actual free-coordinate
parametrization.  Every nonpivot coordinate is preserved literally, while the
pivot coordinates are solved so that `Q (C A) = 0`.

No covariance, Hessian, determinant, or CMP116 activity estimate is asserted
in this module.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

open scoped BigOperators

set_option maxHeartbeats 2000000

variable {d L N' Nc : ℕ}
  [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]

/-- Pointwise expansion of the sparse pivot insertion. -/
theorem cmp96ConstraintPivotInsertion_apply
    (B : CoarsePhysicalOneCochain d N' Nc)
    (p : PhysicalBond d (L * N')) :
    cmp96ConstraintPivotInsertion (L := L) B p =
      ∑ c : PhysicalBond d N',
        if p = cmp96ConstraintPivotBond c then
          ((L : ℝ) ^ (d - 1)) • B c else 0 := by
  simp [cmp96ConstraintPivotInsertion, singlePhysicalBondCochain]

/-- At its own pivot, the sparse insertion reads exactly the corresponding
coarse coordinate. -/
theorem cmp96ConstraintPivotInsertion_apply_pivot
    (B : CoarsePhysicalOneCochain d N' Nc) (c : PhysicalBond d N') :
    cmp96ConstraintPivotInsertion (L := L) B
        (cmp96ConstraintPivotBond c) =
      ((L : ℝ) ^ (d - 1)) • B c := by
  rw [cmp96ConstraintPivotInsertion_apply]
  classical
  rw [Finset.sum_eq_single c]
  · rw [if_pos rfl]
  · intro b _hb hbc
    rw [if_neg]
    intro hpivot
    exact hbc (cmp96ConstraintPivotBond_injective hpivot.symm)
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ c))

/-- The sparse insertion vanishes away from all distinguished bonds. -/
theorem cmp96ConstraintPivotInsertion_apply_of_not_pivot
    (B : CoarsePhysicalOneCochain d N' Nc)
    (p : PhysicalBond d (L * N'))
    (hp : ∀ c : PhysicalBond d N',
      p ≠ cmp96ConstraintPivotBond c) :
    cmp96ConstraintPivotInsertion (L := L) B p = 0 := by
  rw [cmp96ConstraintPivotInsertion_apply]
  apply Finset.sum_eq_zero
  intro c _hc
  rw [if_neg (hp c)]

/-- The physical padded constraint-elimination map `C = I - E Q`. -/
noncomputable def cmp96ConstraintEliminationCLM :
    FinePhysicalOneCochain d L N' Nc →L[ℝ]
      FinePhysicalOneCochain d L N' Nc :=
  ContinuousLinearMap.id ℝ (FinePhysicalOneCochain d L N' Nc) -
    (cmp96ConstraintPivotInsertionCLM
      (d := d) (L := L) (N' := N') (Nc := Nc)).comp
      (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N')

@[simp] theorem cmp96ConstraintEliminationCLM_apply
    (A : FinePhysicalOneCochain d L N' Nc) :
    cmp96ConstraintEliminationCLM (L := L) A =
      A - cmp96ConstraintPivotInsertion (L := L)
        (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N' A) := rfl

/-- `C` solves the block constraint exactly. -/
theorem flatBlockConstraint_comp_cmp96ConstraintEliminationCLM :
    (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N').comp
        (cmp96ConstraintEliminationCLM
          (d := d) (L := L) (N' := N') (Nc := Nc)) = 0 := by
  apply ContinuousLinearMap.ext
  intro A
  change flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
      (cmp96ConstraintEliminationCLM (L := L) A) = 0
  rw [cmp96ConstraintEliminationCLM_apply, map_sub]
  have hright :
      flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
          (cmp96ConstraintPivotInsertion (L := L)
            (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N' A)) =
        flatBlockConstraintQCLM (d := d) (Nc := Nc) L N' A := by
    change (((flatBlockConstraintQCLM (d := d) (Nc := Nc) L N').comp
      (cmp96ConstraintPivotInsertionCLM
        (d := d) (L := L) (N' := N') (Nc := Nc)))
          (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N' A)) = _
    rw [flatBlockConstraint_comp_pivotInsertionCLM]
    rfl
  rw [hright, sub_self]

/-- Pointwise form: every output of `C` satisfies the flat block constraint. -/
theorem flatBlockConstraint_cmp96ConstraintEliminationCLM
    (A : FinePhysicalOneCochain d L N' Nc) :
    flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
        (cmp96ConstraintEliminationCLM (L := L) A) = 0 := by
  change (((flatBlockConstraintQCLM (d := d) (Nc := Nc) L N').comp
    (cmp96ConstraintEliminationCLM
      (d := d) (L := L) (N' := N') (Nc := Nc))) A) = 0
  rw [flatBlockConstraint_comp_cmp96ConstraintEliminationCLM]
  rfl

/-- Constrained fields are fixed pointwise by `C`. -/
theorem cmp96ConstraintEliminationCLM_eq_self_of_mem_ker
    (A : FinePhysicalOneCochain d L N' Nc)
    (hA : flatBlockConstraintQCLM (d := d) (Nc := Nc) L N' A = 0) :
    cmp96ConstraintEliminationCLM (L := L) A = A := by
  rw [cmp96ConstraintEliminationCLM_apply, hA]
  change A - (cmp96ConstraintPivotInsertionCLM
    (d := d) (L := L) (N' := N') (Nc := Nc)) 0 = A
  rw [map_zero, sub_zero]

/-- `C` is a projection, not an arbitrary square extension of the rectangular
free-coordinate map. -/
theorem cmp96ConstraintEliminationCLM_idempotent
    (A : FinePhysicalOneCochain d L N' Nc) :
    cmp96ConstraintEliminationCLM (L := L)
        (cmp96ConstraintEliminationCLM (L := L) A) =
      cmp96ConstraintEliminationCLM (L := L) A := by
  apply cmp96ConstraintEliminationCLM_eq_self_of_mem_ker
  exact flatBlockConstraint_cmp96ConstraintEliminationCLM A

/-- Every nonpivot fine coordinate is left literally unchanged by `C`. -/
theorem cmp96ConstraintEliminationCLM_apply_of_not_pivot
    (A : FinePhysicalOneCochain d L N' Nc)
    (p : PhysicalBond d (L * N'))
    (hp : ∀ c : PhysicalBond d N',
      p ≠ cmp96ConstraintPivotBond c) :
    cmp96ConstraintEliminationCLM (L := L) A p = A p := by
  rw [cmp96ConstraintEliminationCLM_apply, PiLp.sub_apply,
    cmp96ConstraintPivotInsertion_apply_of_not_pivot _ p hp, sub_zero]

/-- The pivot coordinate is changed by precisely the coarse constraint value,
which is the literal elimination formula used to solve `Q B = 0`. -/
theorem cmp96ConstraintEliminationCLM_apply_pivot
    (A : FinePhysicalOneCochain d L N' Nc) (c : PhysicalBond d N') :
    cmp96ConstraintEliminationCLM (L := L) A
        (cmp96ConstraintPivotBond c) =
      A (cmp96ConstraintPivotBond c) -
        ((L : ℝ) ^ (d - 1)) •
          flatBlockConstraintQCLM (d := d) (Nc := Nc) L N' A c := by
  rw [cmp96ConstraintEliminationCLM_apply, PiLp.sub_apply,
    cmp96ConstraintPivotInsertion_apply_pivot]

end YangMills.RG
