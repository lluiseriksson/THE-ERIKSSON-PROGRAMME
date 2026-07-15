/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP96ConstraintElimination
import YangMills.RG.PhysicalPoincareLowModeBlock

/-!
# Volume-uniform norm of the CMP96 constraint coordinates

The distinguished-bond injection has disjoint support, hence its `L²` norm is
exactly `L^(d-1)` times the coarse-field norm.  Combining this with the
certified contraction of the block average in dimensions `d ≥ 3` gives the
explicit volume-independent estimate

`‖C‖ ≤ 1 + L^(d-1)`

for `C = I - E Q`.  The bound depends on the fixed RG block scale and the
dimension, but not on the periodic volume `N'`.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

open scoped BigOperators

set_option maxHeartbeats 2000000

variable {d L N' Nc : ℕ}
  [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]

/-- Exact squared norm of the sparse pivot insertion. -/
theorem norm_sq_cmp96ConstraintPivotInsertion
    (B : CoarsePhysicalOneCochain d N' Nc) :
    ‖cmp96ConstraintPivotInsertion (L := L) B‖ ^ 2 =
      ((L : ℝ) ^ (d - 1)) ^ 2 * ‖B‖ ^ 2 := by
  classical
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  let pivot : PhysicalBond d N' → PhysicalBond d (L * N') :=
    cmp96ConstraintPivotBond (d := d) (L := L) (N' := N')
  let pivots : Finset (PhysicalBond d (L * N')) := Finset.univ.image pivot
  have hsupport :
      (∑ p ∈ pivots, ‖cmp96ConstraintPivotInsertion (L := L) B p‖ ^ 2) =
        ∑ p : PhysicalBond d (L * N'),
          ‖cmp96ConstraintPivotInsertion (L := L) B p‖ ^ 2 := by
    apply Finset.sum_subset (Finset.subset_univ pivots)
    intro p _hp hpn
    have hnot : ∀ c : PhysicalBond d N',
        p ≠ cmp96ConstraintPivotBond c := by
      intro c hpc
      apply hpn
      exact Finset.mem_image.mpr ⟨c, Finset.mem_univ c, hpc.symm⟩
    rw [cmp96ConstraintPivotInsertion_apply_of_not_pivot B p hnot,
      norm_zero, zero_pow]
    norm_num
  calc
    (∑ p : PhysicalBond d (L * N'),
        ‖cmp96ConstraintPivotInsertion (L := L) B p‖ ^ 2) =
        ∑ p ∈ pivots,
          ‖cmp96ConstraintPivotInsertion (L := L) B p‖ ^ 2 := hsupport.symm
    _ = ∑ c : PhysicalBond d N',
          ‖cmp96ConstraintPivotInsertion (L := L) B (pivot c)‖ ^ 2 := by
        rw [show pivots = Finset.univ.image pivot from rfl, Finset.sum_image]
        exact Set.injOn_of_injective cmp96ConstraintPivotBond_injective
    _ = ∑ c : PhysicalBond d N',
          ‖((L : ℝ) ^ (d - 1)) • B c‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro c _hc
        change ‖cmp96ConstraintPivotInsertion (L := L) B
          (cmp96ConstraintPivotBond c)‖ ^ 2 = _
        rw [cmp96ConstraintPivotInsertion_apply_pivot]
    _ = ((L : ℝ) ^ (d - 1)) ^ 2 *
          ∑ c : PhysicalBond d N', ‖B c‖ ^ 2 := by
        simp_rw [norm_smul, Real.norm_of_nonneg (by positivity :
          0 ≤ (L : ℝ) ^ (d - 1)), mul_pow]
        rw [Finset.mul_sum]

/-- Exact norm, with no factor depending on the number of coarse bonds. -/
theorem norm_cmp96ConstraintPivotInsertion
    (B : CoarsePhysicalOneCochain d N' Nc) :
    ‖cmp96ConstraintPivotInsertion (L := L) B‖ =
      (L : ℝ) ^ (d - 1) * ‖B‖ := by
  have hsq := norm_sq_cmp96ConstraintPivotInsertion (L := L) B
  have hscale : 0 ≤ (L : ℝ) ^ (d - 1) := by positivity
  have hleft := norm_nonneg (cmp96ConstraintPivotInsertion (L := L) B)
  have hright := norm_nonneg B
  have hsq' : ‖cmp96ConstraintPivotInsertion (L := L) B‖ ^ 2 =
      ((L : ℝ) ^ (d - 1) * ‖B‖) ^ 2 := by
    rw [hsq, mul_pow]
  exact (sq_eq_sq₀ hleft (mul_nonneg hscale hright)).mp hsq'

/-- Operator norm of the right inverse. -/
theorem norm_cmp96ConstraintPivotInsertionCLM_le :
    ‖cmp96ConstraintPivotInsertionCLM
        (d := d) (L := L) (N' := N') (Nc := Nc)‖ ≤
      (L : ℝ) ^ (d - 1) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro B
  rw [cmp96ConstraintPivotInsertionCLM_apply,
    norm_cmp96ConstraintPivotInsertion]

/-- The physical block constraint is nonexpansive for `d ≥ 3`. -/
theorem norm_flatBlockConstraintQCLM_apply_le
    (hd : 3 ≤ d) (A : FinePhysicalOneCochain d L N' Nc) :
    ‖flatBlockConstraintQCLM (d := d) (Nc := Nc) L N' A‖ ≤ ‖A‖ := by
  have hsq := norm_sq_flatBlockConstraintQCLM_le_inv_mul hd A
  have hLone : (1 : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  have hinv : (L : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hLone
  have hsq' :
      ‖flatBlockConstraintQCLM (d := d) (Nc := Nc) L N' A‖ ^ 2 ≤
        ‖A‖ ^ 2 := by
    calc
      _ ≤ (L : ℝ)⁻¹ * ‖A‖ ^ 2 := hsq
      _ ≤ 1 * ‖A‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hinv (sq_nonneg ‖A‖)
      _ = ‖A‖ ^ 2 := one_mul _
  nlinarith [norm_nonneg
    (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N' A), norm_nonneg A]

/-- Volume-uniform application bound for the physical elimination map. -/
theorem norm_cmp96ConstraintEliminationCLM_apply_le
    (hd : 3 ≤ d) (A : FinePhysicalOneCochain d L N' Nc) :
    ‖cmp96ConstraintEliminationCLM (L := L) A‖ ≤
      (1 + (L : ℝ) ^ (d - 1)) * ‖A‖ := by
  rw [cmp96ConstraintEliminationCLM_apply]
  calc
    ‖A - cmp96ConstraintPivotInsertion (L := L)
        (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N' A)‖
        ≤ ‖A‖ + ‖cmp96ConstraintPivotInsertion (L := L)
          (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N' A)‖ := norm_sub_le _ _
    _ = ‖A‖ + (L : ℝ) ^ (d - 1) *
          ‖flatBlockConstraintQCLM (d := d) (Nc := Nc) L N' A‖ := by
        rw [norm_cmp96ConstraintPivotInsertion]
    _ ≤ ‖A‖ + (L : ℝ) ^ (d - 1) * ‖A‖ := by
        gcongr
        exact norm_flatBlockConstraintQCLM_apply_le hd A
    _ = (1 + (L : ℝ) ^ (d - 1)) * ‖A‖ := by ring

/-- Explicit volume-independent operator norm of `C`. -/
theorem norm_cmp96ConstraintEliminationCLM_le
    (hd : 3 ≤ d) :
    ‖cmp96ConstraintEliminationCLM
        (d := d) (L := L) (N' := N') (Nc := Nc)‖ ≤
      1 + (L : ℝ) ^ (d - 1) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact norm_cmp96ConstraintEliminationCLM_apply_le hd

end YangMills.RG
