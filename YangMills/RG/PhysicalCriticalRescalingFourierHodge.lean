/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalCriticalRescalingFourierCochain

/-!
# Exact flat-Hodge energy of the Fourier transverse cochain
-/

namespace YangMills.RG

open Matrix Module

theorem norm_sq_covariantD1CLM_blockFourierModeCochain_of_ne
    (d L N' Nc : ℕ) [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (hL : 2 ≤ L) (hNc : 2 ≤ Nc)
    (i j : Fin d) (hij : i ≠ j) :
    ‖covariantD1CLM ρ (trivialPhysicalGaugeBackground d (L * N') Nc)
        (blockFourierModeCochain d L N' Nc hNc i j)‖ ^ 2 =
      (((L * N' : ℕ) : ℝ) ^ d) * blockFourierEigenvalue L := by
  rw [PiLp.norm_sq_eq_of_L2]
  let D := covariantD1CLM ρ
    (trivialPhysicalGaugeBackground d (L * N') Nc)
      (blockFourierModeCochain d L N' Nc hNc i j)
  let e := concretePlaquetteEquivOrderedPair d (L * N')
  have hsplit :
      (∑ p : ConcretePlaquette d (L * N'), ‖D p‖ ^ 2) =
        ∑ z : FinBox d (L * N') × OrderedDirectionPair d,
          ‖D (e.symm z)‖ ^ 2 := by
    have h := e.sum_comp (fun z => ‖D (e.symm z)‖ ^ 2)
    simpa using h
  rw [hsplit, Fintype.sum_prod_type]
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · let q0 : OrderedDirectionPair d := ⟨(i, j), hijlt⟩
    have hpoint : ∀ (x : FinBox d (L * N')) (q : OrderedDirectionPair d),
        ‖D (e.symm (x, q))‖ ^ 2 =
          if q = q0 then
            ‖blockFourierProfile L N' Nc hNc (x j) -
              blockFourierProfile L N' Nc hNc ((x.shift j) j)‖ ^ 2
          else 0 := by
      intro x q
      change
        ‖covariantD1CLM ρ (trivialPhysicalGaugeBackground d (L * N') Nc)
          (blockFourierModeCochain d L N' Nc hNc i j)
          ⟨x, q.1.1, q.1.2, q.2⟩‖ ^ 2 = _
      by_cases hq : q = q0
      · subst q
        rw [if_pos rfl, covariantD1CLM_blockFourierModeCochain_apply]
        simp only [q0, if_pos]
      · rw [if_neg hq, covariantD1CLM_blockFourierModeCochain_apply]
        by_cases h1 : q.1.1 = i
        · have h2 : q.1.2 ≠ i := by
            intro h2
            have := q.2
            omega
          have hnotj : q.1.2 ≠ j := by
            intro hdir
            apply hq
            apply Subtype.ext
            exact Prod.ext h1 hdir
          simp only [h1, h2, if_true, if_false]
          have hcoord : (x.shift q.1.2) j = x j := by
            simp [FinBox.shift, Ne.symm hnotj]
          rw [hcoord, sub_self, norm_zero]
          norm_num
        · by_cases h2 : q.1.2 = i
          · have hnotj : q.1.1 ≠ j := by
              intro hdir
              have := q.2
              omega
            simp only [h1, h2, if_false, if_true]
            have hcoord : (x.shift q.1.1) j = x j := by
              simp [FinBox.shift, Ne.symm hnotj]
            rw [hcoord, sub_self, norm_zero]
            norm_num
          · simp [h1, h2]
    rw [Finset.sum_congr rfl (fun x _ =>
      Finset.sum_congr rfl (fun q _ => hpoint x q))]
    simp only [Finset.sum_ite_eq' Finset.univ q0, Finset.mem_univ, if_true]
    exact sum_finBox_blockFourierProfile_shift_diff_norm_sq
      d L N' Nc hL hNc j
  · let q0 : OrderedDirectionPair d := ⟨(j, i), hjilt⟩
    have hpoint : ∀ (x : FinBox d (L * N')) (q : OrderedDirectionPair d),
        ‖D (e.symm (x, q))‖ ^ 2 =
          if q = q0 then
            ‖blockFourierProfile L N' Nc hNc (x j) -
              blockFourierProfile L N' Nc hNc ((x.shift j) j)‖ ^ 2
          else 0 := by
      intro x q
      change
        ‖covariantD1CLM ρ (trivialPhysicalGaugeBackground d (L * N') Nc)
          (blockFourierModeCochain d L N' Nc hNc i j)
          ⟨x, q.1.1, q.1.2, q.2⟩‖ ^ 2 = _
      by_cases hq : q = q0
      · subst q
        rw [if_pos rfl, covariantD1CLM_blockFourierModeCochain_apply]
        simp only [q0, if_neg (Ne.symm hij), if_pos]
        rw [norm_sub_rev]
      · rw [if_neg hq, covariantD1CLM_blockFourierModeCochain_apply]
        by_cases h1 : q.1.1 = i
        · have h2 : q.1.2 ≠ i := by
            intro h2
            have := q.2
            omega
          have hnotj : q.1.2 ≠ j := by
            intro hdir
            have := q.2
            omega
          simp only [h1, h2, if_true, if_false]
          have hcoord : (x.shift q.1.2) j = x j := by
            simp [FinBox.shift, Ne.symm hnotj]
          rw [hcoord, sub_self, norm_zero]
          norm_num
        · by_cases h2 : q.1.2 = i
          · have hnotj : q.1.1 ≠ j := by
              intro hdir
              apply hq
              apply Subtype.ext
              exact Prod.ext hdir h2
            simp only [h1, h2, if_false, if_true]
            have hcoord : (x.shift q.1.1) j = x j := by
              simp [FinBox.shift, Ne.symm hnotj]
            rw [hcoord, sub_self, norm_zero]
            norm_num
          · simp [h1, h2]
    rw [Finset.sum_congr rfl (fun x _ =>
      Finset.sum_congr rfl (fun q _ => hpoint x q))]
    simp only [Finset.sum_ite_eq' Finset.univ q0, Finset.mem_univ, if_true]
    exact sum_finBox_blockFourierProfile_shift_diff_norm_sq
      d L N' Nc hL hNc j

theorem flatGaugeHodgeK0_inner_blockFourierModeCochain_of_ne
    (d L N' Nc : ℕ) [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (hL : 2 ≤ L) (hNc : 2 ≤ Nc)
    (i j : Fin d) (hij : i ≠ j) :
    inner ℝ (blockFourierModeCochain d L N' Nc hNc i j)
        (flatGaugeHodgeK0CLM d (L * N') Nc ρ
          (blockFourierModeCochain d L N' Nc hNc i j)) =
      (((L * N' : ℕ) : ℝ) ^ d) * blockFourierEigenvalue L := by
  rw [flatGaugeHodgeK0_inner_right]
  rw [norm_sq_covariantD1CLM_blockFourierModeCochain_of_ne
      d L N' Nc ρ hL hNc i j hij,
    gaugeConstraintQCLM_blockFourierModeCochain_eq_zero_of_ne
      d L N' Nc ρ hNc i j hij,
    norm_zero]
  norm_num

end YangMills.RG
