/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP96ConstraintPivot

/-!
# A local right inverse of the flat block constraint

The distinguished bonds `b₀(c)` give a sparse insertion from coarse bond
fields to fine bond fields.  Multiplication by `L^(d-1)` compensates exactly
for the `L` path multiplicity and the `L^d` block-average normalization.
Consequently this insertion is a right inverse of the physical flat block
constraint `Q`.

This is the algebraic ingredient in Bałaban's coordinate elimination
`B = C \widetilde B`: it permits the pivot coordinate to be solved without
mixing different coarse constraints.  The reduced-coordinate domain and the
final elimination map `C` are constructed in the next module.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

open scoped BigOperators

set_option maxHeartbeats 2000000

variable {d L N' Nc : ℕ}
  [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]

/-- Sparse insertion on the distinguished bonds, with the exact scale needed
to invert the block average. -/
noncomputable def cmp96ConstraintPivotInsertion
    (B : CoarsePhysicalOneCochain d N' Nc) :
    FinePhysicalOneCochain d L N' Nc :=
  ∑ c : PhysicalBond d N',
    singlePhysicalBondCochain
      (cmp96ConstraintPivotBond (d := d) (L := L) (N' := N') c)
      (((L : ℝ) ^ (d - 1)) • B c)

theorem cmp96ConstraintPivotInsertion_add
    (B B' : CoarsePhysicalOneCochain d N' Nc) :
    cmp96ConstraintPivotInsertion (L := L) (B + B') =
      cmp96ConstraintPivotInsertion (L := L) B +
        cmp96ConstraintPivotInsertion (L := L) B' := by
  apply PiLp.ext
  intro p
  simp [cmp96ConstraintPivotInsertion, singlePhysicalBondCochain,
    smul_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _hc
  by_cases hp : p = cmp96ConstraintPivotBond c <;> simp [hp, smul_add]

theorem cmp96ConstraintPivotInsertion_smul
    (a : ℝ) (B : CoarsePhysicalOneCochain d N' Nc) :
    cmp96ConstraintPivotInsertion (L := L) (a • B) =
      a • cmp96ConstraintPivotInsertion (L := L) B := by
  apply PiLp.ext
  intro p
  simp [cmp96ConstraintPivotInsertion, singlePhysicalBondCochain,
    smul_smul, Finset.smul_sum, mul_comm]

/-- Bundled continuous-linear sparse insertion.  Continuity is automatic in
the finite-dimensional physical cochain spaces. -/
noncomputable def cmp96ConstraintPivotInsertionCLM :
    CoarsePhysicalOneCochain d N' Nc →L[ℝ]
      FinePhysicalOneCochain d L N' Nc :=
  LinearMap.toContinuousLinearMap
    { toFun := cmp96ConstraintPivotInsertion (d := d) (L := L) (N' := N')
      map_add' := cmp96ConstraintPivotInsertion_add (L := L)
      map_smul' := cmp96ConstraintPivotInsertion_smul (L := L) }

@[simp] theorem cmp96ConstraintPivotInsertionCLM_apply
    (B : CoarsePhysicalOneCochain d N' Nc) :
    cmp96ConstraintPivotInsertionCLM (d := d) (L := L) (N' := N') B =
      cmp96ConstraintPivotInsertion (L := L) B := rfl

/-- Scalar cancellation behind the right-inverse identity. -/
theorem cmp96ConstraintPivot_scale_cancel :
    ((L : ℝ) ^ d)⁻¹ * ((L : ℝ) * (L : ℝ) ^ (d - 1)) = 1 := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hL : (L : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne L)
  have hpow : (L : ℝ) * (L : ℝ) ^ (d - 1) = (L : ℝ) ^ d := by
    calc
      (L : ℝ) * (L : ℝ) ^ (d - 1) =
          (L : ℝ) ^ (d - 1) * (L : ℝ) := mul_comm _ _
      _ = (L : ℝ) ^ ((d - 1) + 1) := (pow_succ _ _).symm
      _ = (L : ℝ) ^ d := by congr 1 <;> omega
  rw [hpow, inv_mul_cancel₀ (pow_ne_zero d hL)]

/-- The distinguished-bond insertion is an exact right inverse of the flat
physical block constraint. -/
theorem flatBlockConstraint_comp_pivotInsertionCLM :
    (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N').comp
        (cmp96ConstraintPivotInsertionCLM
          (d := d) (L := L) (N' := N') (Nc := Nc)) =
      ContinuousLinearMap.id ℝ (CoarsePhysicalOneCochain d N' Nc) := by
  apply ContinuousLinearMap.ext
  intro B
  apply PiLp.ext
  intro b
  change flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
      (cmp96ConstraintPivotInsertion (L := L) B) b = B b
  rw [cmp96ConstraintPivotInsertion, map_sum]
  let f : PhysicalBond d N' → CoarsePhysicalOneCochain d N' Nc := fun c =>
    flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
      (singlePhysicalBondCochain
        (cmp96ConstraintPivotBond (d := d) (L := L) (N' := N') c)
        (((L : ℝ) ^ (d - 1)) • B c))
  have eval_sum (s : Finset (PhysicalBond d N')) :
      (∑ c ∈ s, f c) b = ∑ c ∈ s, f c b := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert c s hc ih =>
        rw [Finset.sum_insert hc, Finset.sum_insert hc, PiLp.add_apply, ih]
  change (∑ c : PhysicalBond d N', f c) b = B b
  rw [eval_sum Finset.univ]
  dsimp only [f]
  change (∑ c : PhysicalBond d N',
      flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
        (singlePhysicalBondCochain
          (cmp96ConstraintPivotBond (d := d) (L := L) (N' := N') c)
          (((L : ℝ) ^ (d - 1)) • B c)) b) = B b
  simp_rw [flatBlockConstraint_pivot_probe_apply]
  rw [Finset.sum_eq_single b]
  · rw [if_pos rfl]
    simp only [smul_smul]
    rw [show ((L : ℝ) ^ d)⁻¹ *
        ((L : ℝ) * (L : ℝ) ^ (d - 1)) = 1 from
      cmp96ConstraintPivot_scale_cancel (d := d) (L := L)]
    exact one_smul ℝ (B b)
  · intro c _hc hcb
    rw [if_neg]
    exact fun hbc => hcb hbc.symm
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ b))

end YangMills.RG
