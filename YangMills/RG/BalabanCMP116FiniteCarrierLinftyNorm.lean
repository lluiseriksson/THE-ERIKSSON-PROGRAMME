/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Analysis.Matrix.Normed
import YangMills.RG.BalabanCMP116Eq214FiniteCarrierFactorization

/-!
# L-infinity norm of finite-carrier restriction matrices

Zero extension and coordinate restriction have row-sum operator norm at most
one.  The statement includes the empty carrier and is independent of both the
ambient and carrier cardinalities.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

/-- Zero extension from a finite coordinate carrier is nonexpansive in the
matrix L-infinity operator norm. -/
theorem linfty_opNorm_cmp116FinsetColumnInclusion_le_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) :
    ‖cmp116FinsetColumnInclusion (α := ℂ) S‖ ≤ 1 := by
  classical
  rw [Matrix.linfty_opNorm_def]
  change
    (↑((Finset.univ : Finset ι).sup fun i : ι =>
      ∑ s : ↥S,
        ‖cmp116FinsetColumnInclusion (α := ℂ) S i s‖₊) : ℝ) ≤
      ↑(1 : NNReal)
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro i hi
  by_cases hiS : i ∈ S
  · let s0 : ↥S := ⟨i, hiS⟩
    calc
      (∑ s : ↥S,
          ‖cmp116FinsetColumnInclusion (α := ℂ) S i s‖₊) =
          ‖cmp116FinsetColumnInclusion (α := ℂ) S i s0‖₊ := by
        apply Finset.sum_eq_single s0
        · intro s _hs hne
          have his : i ≠ (s : ι) := by
            intro h
            apply hne
            apply Subtype.ext
            simpa [s0] using h.symm
          simp [cmp116FinsetColumnInclusion, his]
        · intro hnot
          exact (hnot (Finset.mem_univ s0)).elim
      _ ≤ 1 := by simp [cmp116FinsetColumnInclusion, s0]
  · have his : ∀ s : ↥S, i ≠ (s : ι) := by
      intro s h
      apply hiS
      rw [h]
      exact s.property
    simp only [cmp116FinsetColumnInclusion, his, if_false, nnnorm_zero,
      Finset.sum_const_zero]
    exact bot_le

/-- Restriction to a finite coordinate carrier is nonexpansive in the matrix
L-infinity operator norm. -/
theorem linfty_opNorm_cmp116FinsetCoordinateRestriction_le_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) :
    ‖cmp116FinsetCoordinateRestriction (α := ℂ) S‖ ≤ 1 := by
  classical
  rw [Matrix.linfty_opNorm_def]
  change
    (↑((Finset.univ : Finset ↥S).sup fun s : ↥S =>
      ∑ i : ι,
        ‖cmp116FinsetCoordinateRestriction (α := ℂ) S s i‖₊) : ℝ) ≤
      ↑(1 : NNReal)
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro s hs
  calc
    (∑ i : ι,
        ‖cmp116FinsetCoordinateRestriction (α := ℂ) S s i‖₊) =
        ‖cmp116FinsetCoordinateRestriction (α := ℂ) S s (s : ι)‖₊ := by
      apply Finset.sum_eq_single (s : ι)
      · intro i _hi hne
        simp [cmp116FinsetCoordinateRestriction, hne.symm]
      · intro hnot
        exact (hnot (Finset.mem_univ (s : ι))).elim
    _ ≤ 1 := by simp [cmp116FinsetCoordinateRestriction]

end

end YangMills.RG
