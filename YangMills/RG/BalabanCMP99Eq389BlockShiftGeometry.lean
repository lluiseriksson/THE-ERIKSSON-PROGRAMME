/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99Eq389CovariantLinkGreenBound
import YangMills.RG.PhysicalShellLocalityDiv

/-!
# PRE-VALIDATION: block geometry for the first CMP99 (3.89) species

The source of this module is present, but its `.olean` has not yet been
materialized and its declarations have not yet been verified by the Lean
compiler.

The sealed regional-Green link bound retains the exact block metric at each
backward-shifted fine site.  This module proves from the literal quotient map
that one such fine step either remains in the same block or crosses exactly
one backward coarse face.  No favorable metric comparison is accepted from a
caller.
-/

namespace YangMills.RG

open YangMills

variable {d m n : ℕ} [NeZero m] [NeZero n]

/-- One backward fine step either stays in its block or crosses precisely the
corresponding backward coarse face. -/
theorem blockSite_shiftBack_eq_self_or_shiftBack
    (x : FinBox d (m * n)) (i : Fin d) :
    blockSite m n (x.shiftBack i) = blockSite m n x ∨
      blockSite m n (x.shiftBack i) = (blockSite m n x).shiftBack i := by
  by_cases hrem : (x i).val % m = 0
  · right
    funext j
    by_cases hji : j = i
    · subst j
      apply Fin.ext
      simp only [blockSite_val, FinBox.shiftBack, if_pos]
      have hm : 0 < m := NeZero.pos m
      have hn : 0 < n := NeZero.pos n
      have hx : (x i).val < m * n := (x i).isLt
      have hmn : 0 < m * n := Nat.mul_pos hm hn
      change
        (((x i).val + m * n - 1) % (m * n)) / m =
          (((x i).val / m + n - 1) % n)
      by_cases hx0 : (x i).val = 0
      · have hdiv : (m * n - 1) / m = n - 1 := by
          apply Nat.div_eq_of_lt_le
          · have hlt : (n - 1) * m < n * m :=
              Nat.mul_lt_mul_of_pos_right (by omega) hm
            rw [Nat.mul_comm n m] at hlt
            omega
          · rw [show n - 1 + 1 = n by omega, Nat.mul_comm n m]
            omega
        rw [hx0, Nat.zero_add, Nat.mod_eq_of_lt (by omega : m * n - 1 < m * n),
          Nat.zero_div, Nat.zero_add, hdiv,
          Nat.mod_eq_of_lt (by omega : n - 1 < n)]
      · have hpos : 0 < (x i).val := Nat.pos_of_ne_zero hx0
        have hpred :
            ((x i).val + m * n - 1) % (m * n) = (x i).val - 1 := by
          rw [show (x i).val + m * n - 1 = ((x i).val - 1) + m * n by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : (x i).val - 1 < m * n)]
        have hdecomp := Nat.div_add_mod (x i).val m
        have hkm : ((x i).val / m) * m = (x i).val := by
          rw [hrem, Nat.add_zero] at hdecomp
          exact hdecomp
        have hkpos : 0 < (x i).val / m := by
          by_contra hk
          have hk0 : (x i).val / m = 0 := Nat.eq_zero_of_not_pos hk
          rw [hk0, Nat.zero_mul] at hkm
          omega
        have hklt : (x i).val / m < n := Nat.div_lt_of_lt_mul hx
        have hdivpred :
            ((x i).val - 1) / m = (x i).val / m - 1 := by
          apply Nat.div_eq_of_lt_le
          · have hlt : ((x i).val / m - 1) * m <
                ((x i).val / m) * m :=
              Nat.mul_lt_mul_of_pos_right (by omega) hm
            rw [hkm] at hlt
            omega
          · rw [show (x i).val / m - 1 + 1 = (x i).val / m by omega, hkm]
            omega
        have hcoarse :
            ((x i).val / m + n - 1) % n = (x i).val / m - 1 := by
          rw [show (x i).val / m + n - 1 =
              ((x i).val / m - 1) + n by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [hpred, hdivpred, hcoarse]
    · apply Fin.ext
      simp only [blockSite_val, FinBox.shiftBack, if_neg hji]
  · left
    funext j
    by_cases hji : j = i
    · subst j
      apply Fin.ext
      simp only [blockSite_val, FinBox.shiftBack, if_pos]
      have hm : 0 < m := NeZero.pos m
      have hn : 0 < n := NeZero.pos n
      have hx : (x i).val < m * n := (x i).isLt
      change
        (((x i).val + m * n - 1) % (m * n)) / m = (x i).val / m
      have hrempos : 0 < (x i).val % m := Nat.pos_of_ne_zero hrem
      have hpos : 0 < (x i).val := by
        have hmodle := Nat.mod_le (x i).val m
        omega
      have hpred :
          ((x i).val + m * n - 1) % (m * n) = (x i).val - 1 := by
        rw [show (x i).val + m * n - 1 = ((x i).val - 1) + m * n by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : (x i).val - 1 < m * n)]
      have hdecomp := Nat.div_add_mod (x i).val m
      have hrem_lt := Nat.mod_lt (x i).val hm
      have hdivsame : ((x i).val - 1) / m = (x i).val / m := by
        apply Nat.div_eq_of_lt_le
        · rw [Nat.mul_comm]
          omega
        · rw [Nat.add_mul, one_mul]
          omega
      rw [hpred, hdivsame]
    · apply Fin.ext
      simp only [blockSite_val, FinBox.shiftBack, if_neg hji]

/-- The source block owner changes by Chebyshev distance at most one under a
single backward fine step. -/
theorem finBoxDist_blockSite_shiftBack_le_one
    (x : FinBox d (m * n)) (i : Fin d) :
    finBoxDist (blockSite m n x) (blockSite m n (x.shiftBack i)) ≤ 1 := by
  rcases blockSite_shiftBack_eq_self_or_shiftBack (m := m) (n := n) x i with
    hsame | hback
  · rw [hsame, finBoxDist_self]
    exact Nat.zero_le _
  · rw [hback]
    exact finBoxDist_shiftBack_le (blockSite m n x) i

end YangMills.RG
