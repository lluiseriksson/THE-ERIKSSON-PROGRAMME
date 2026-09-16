/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP96ConstraintNorm
import YangMills.RG.PhysicalExponentialKernelComposition

/-!
# Physical locality of the CMP96 constraint elimination

The padded constraint coordinate map

`C = I - E Q`

changes only the distinguished pivot bond of a coarse constraint.  Every fine
bond read by that constraint lies in the same length-`L` block-line stencil as
the pivot, hence within `physicalBondDist ≤ 3L`.  This gives a genuine
volume-uniform finite-range theorem for `C`, not merely its previously proved
operator-norm bound.

Combining the finite range with `‖C‖ ≤ 1 + L^(d-1)` yields the exponential
kernel certificate consumed by the physical `R₃` telescope.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 2000000

variable {d L N' Nc : ℕ}
  [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc] [NeZero (L * N')]

/-- Every line sample read by a coarse constraint is within `3L` of that
constraint's distinguished pivot bond. -/
theorem physicalBondDist_sample_pivot_le
    (c : PhysicalBond d N') (x : FinBox d (L * N')) {k : ℕ}
    (hx : x ∈ blockOf L N' c.1) (hk : k < L) :
    physicalBondDist
        (((fun z => FinBox.shift z c.2)^[k] x, c.2) :
          PhysicalBond d (L * N'))
        (cmp96ConstraintPivotBond (d := d) (L := L) (N' := N') c)
      ≤ 3 * L := by
  have hL : L - 1 < L := by omega
  have hsites :
      finBoxDist
          ((fun z => FinBox.shift z c.2)^[k] x)
          ((fun z => FinBox.shift z c.2)^[L - 1]
            (blockBasepoint L N' c.1))
        ≤ 3 * L := by
    apply sample_sites_dist_le x (blockBasepoint L N' c.1) c.2 k (L - 1)
      hk hL
    rw [(mem_blockOf L N' c.1 x).mp hx, blockSite_blockBasepoint]
  simpa [physicalBondDist, cmp96ConstraintPivotBond,
    cmp96ConstraintPivotSource, max_eq_left (Nat.zero_le _)] using hsites

/-- A single-bond probe farther than `3L` from the pivot is invisible to the
corresponding coarse constraint row. -/
theorem flatBlockConstraint_single_apply_eq_zero_of_pivot_far
    (c : PhysicalBond d N') (source : PhysicalBond d (L * N'))
    (v : SUNLieCoord Nc)
    (hfar : 3 * L <
      physicalBondDist
        (cmp96ConstraintPivotBond (d := d) (L := L) (N' := N') c)
        source) :
    flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
        (singlePhysicalBondCochain source v) c = 0 := by
  apply flatBlockConstraint_single_eq_zero source v c
  intro x hx k hk
  intro heq
  have hnear :=
    physicalBondDist_sample_pivot_le
      (d := d) (L := L) (N' := N')
      c x hx (Finset.mem_range.mp hk)
  rw [heq, physicalBondDist_comm] at hnear
  omega

/-- The physical constraint-elimination operator has range `3L`, uniformly
in the periodic volume. -/
theorem cmp96ConstraintEliminationCLM_finiteRange :
    PhysicalCovarianceFiniteRange
      (cmp96ConstraintEliminationCLM
        (d := d) (L := L) (N' := N') (Nc := Nc))
      physicalBondDist (3 * L) := by
  intro source target v hfar
  classical
  by_cases hpivot : ∃ c : PhysicalBond d N',
      target = cmp96ConstraintPivotBond (d := d) (L := L) (N' := N') c
  · rcases hpivot with ⟨c, rfl⟩
    have hne :
        cmp96ConstraintPivotBond (d := d) (L := L) (N' := N') c ≠ source := by
      intro heq
      subst source
      simpa using hfar
    rw [cmp96ConstraintEliminationCLM_apply_pivot,
      singlePhysicalBondCochain_of_ne v hne,
      flatBlockConstraint_single_apply_eq_zero_of_pivot_far
        (c := c) (source := source) v hfar,
      smul_zero, sub_zero]
  · have hnot : ∀ c : PhysicalBond d N',
        target ≠ cmp96ConstraintPivotBond (d := d) (L := L) (N' := N') c := by
      intro c heq
      exact hpivot ⟨c, heq⟩
    rw [cmp96ConstraintEliminationCLM_apply_of_not_pivot _ target hnot]
    apply singlePhysicalBondCochain_of_ne
    intro heq
    subst target
    simpa using hfar

/-- The volume-uniform operator norm of `C` supplies a constant block-kernel
bound. -/
theorem cmp96ConstraintEliminationCLM_kernelBound
    (hd : 3 ≤ d) :
    PhysicalCovarianceKernelBound
      (cmp96ConstraintEliminationCLM
        (d := d) (L := L) (N' := N') (Nc := Nc))
      (fun _ _ => 1 + (L : ℝ) ^ (d - 1)) := by
  intro source target v
  calc
    ‖cmp96ConstraintEliminationCLM
        (d := d) (L := L) (N' := N') (Nc := Nc)
        (singlePhysicalBondCochain source v) target‖
        ≤
      ‖cmp96ConstraintEliminationCLM
        (d := d) (L := L) (N' := N') (Nc := Nc)‖ * ‖v‖ :=
      physicalCovarianceKernelBound_const_opNorm
        (cmp96ConstraintEliminationCLM
          (d := d) (L := L) (N' := N') (Nc := Nc))
        source target v
    _ ≤ (1 + (L : ℝ) ^ (d - 1)) * ‖v‖ :=
      mul_le_mul_of_nonneg_right
        (norm_cmp96ConstraintEliminationCLM_le
          (d := d) (L := L) (N' := N') (Nc := Nc) hd)
        (norm_nonneg v)

/-- Explicit exponential localization of the physical elimination map. -/
theorem cmp96ConstraintEliminationCLM_exponentialKernelBound
    (hd : 3 ≤ d) {κ : ℝ} (hκ : 0 < κ) :
    PhysicalCovarianceExponentialKernelBound
      (cmp96ConstraintEliminationCLM
        (d := d) (L := L) (N' := N') (Nc := Nc))
      physicalBondDist
      ((1 + (L : ℝ) ^ (d - 1)) *
        Real.exp (κ * ((3 * L : ℕ) : ℝ)))
      κ := by
  apply physicalCovarianceExponentialKernelBound_of_finiteRange
      physicalBondDist
      (show 0 ≤ 1 + (L : ℝ) ^ (d - 1) by positivity)
      hκ
      (cmp96ConstraintEliminationCLM
        (d := d) (L := L) (N' := N') (Nc := Nc))
  · exact cmp96ConstraintEliminationCLM_finiteRange
  · exact cmp96ConstraintEliminationCLM_kernelBound hd

end

end YangMills.RG
