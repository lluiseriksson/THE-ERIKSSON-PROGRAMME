/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib

/-!
# Finite transported-mean control for the CMP99 source average

This file isolates the Hilbert-space estimate behind one source block.  A
normalized finite mean controls the constant mode, while deviations from one
common base point control the fluctuation.  The theorem is independent of the
lattice and will be consumed with the literal covariant contour defects.
-/

namespace YangMills.RG

open scoped BigOperators RealInnerProductSpace

noncomputable section

/-- Three-term scalar Cauchy--Schwarz in the form used below. -/
theorem sq_add_add_le_three_mul_sum_sq (a b c : ℝ) :
    (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]

/-- A normalized finite mean and deviations from a common base point control
the full sum of squares.  The constants are deliberately elementary; their
role is to preserve volume-uniformity, not sharpness. -/
theorem sum_norm_sq_le_six_sum_base_defect_sq_add_three_card_mean_sq
    {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w : ℝ) (hw : 0 ≤ w)
    (hnorm : w * (Fintype.card I : ℝ) = 1)
    (base : E) (v : I → E) :
    (∑ i : I, ‖v i‖ ^ 2) ≤
      6 * (∑ i : I, ‖base - v i‖ ^ 2) +
        3 * (Fintype.card I : ℝ) * ‖w • (∑ i : I, v i)‖ ^ 2 := by
  let delta : I → E := fun i => base - v i
  let mean : E := w • (∑ i : I, v i)
  have hbase : base = mean + w • (∑ i : I, delta i) := by
    calc
      base = (w * (Fintype.card I : ℝ)) • base := by rw [hnorm, one_smul]
      _ = w • ((Fintype.card I : ℝ) • base) := by rw [mul_smul]
      _ = w • (∑ _i : I, base) := by
        rw [Finset.sum_const, Finset.card_univ,
          ← Nat.cast_smul_eq_nsmul ℝ]
      _ = w • ((∑ i : I, v i) + ∑ i : I, delta i) := by
        congr 1
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _hi
        simp [delta]
      _ = mean + w • (∑ i : I, delta i) := by
        rw [smul_add]
  have hpoint : ∀ i : I,
      ‖v i‖ ≤ ‖mean‖ + ‖w • (∑ j : I, delta j)‖ + ‖delta i‖ := by
    intro i
    have hv : v i = mean + w • (∑ j : I, delta j) - delta i := by
      rw [← hbase]
      simp [delta]
    rw [hv]
    calc
      ‖mean + w • (∑ j : I, delta j) - delta i‖ ≤
          ‖mean + w • (∑ j : I, delta j)‖ + ‖delta i‖ :=
        norm_sub_le _ _
      _ ≤ ‖mean‖ + ‖w • (∑ j : I, delta j)‖ + ‖delta i‖ := by
        gcongr
        exact norm_add_le _ _
  have hpointSq : ∀ i : I,
      ‖v i‖ ^ 2 ≤
        3 * (‖mean‖ ^ 2 +
          ‖w • (∑ j : I, delta j)‖ ^ 2 + ‖delta i‖ ^ 2) := by
    intro i
    calc
      ‖v i‖ ^ 2 ≤
          (‖mean‖ + ‖w • (∑ j : I, delta j)‖ + ‖delta i‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hpoint i)
      _ ≤ 3 * (‖mean‖ ^ 2 +
          ‖w • (∑ j : I, delta j)‖ ^ 2 + ‖delta i‖ ^ 2) :=
        sq_add_add_le_three_mul_sum_sq _ _ _
  have hsumNorm : ‖∑ i : I, delta i‖ ≤ ∑ i : I, ‖delta i‖ :=
    norm_sum_le _ _
  have hsumNormSq : ‖∑ i : I, delta i‖ ^ 2 ≤
      (Fintype.card I : ℝ) * ∑ i : I, ‖delta i‖ ^ 2 := by
    calc
      ‖∑ i : I, delta i‖ ^ 2 ≤ (∑ i : I, ‖delta i‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mpr
          hsumNorm
      _ ≤ (Fintype.card I : ℝ) * ∑ i : I, ‖delta i‖ ^ 2 := by
        simpa using
          (sq_sum_le_card_mul_sum_sq
            (s := (Finset.univ : Finset I))
            (f := fun i : I => ‖delta i‖))
  have hmeanDefect :
      (Fintype.card I : ℝ) * ‖w • (∑ i : I, delta i)‖ ^ 2 ≤
        ∑ i : I, ‖delta i‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw, mul_pow]
    have hncard : 0 ≤ (Fintype.card I : ℝ) := by positivity
    calc
      (Fintype.card I : ℝ) *
          (w ^ 2 * ‖∑ i : I, delta i‖ ^ 2) ≤
        (Fintype.card I : ℝ) *
          (w ^ 2 * ((Fintype.card I : ℝ) *
            ∑ i : I, ‖delta i‖ ^ 2)) := by
              gcongr
      _ = (w * (Fintype.card I : ℝ)) ^ 2 *
          ∑ i : I, ‖delta i‖ ^ 2 := by ring
      _ = ∑ i : I, ‖delta i‖ ^ 2 := by rw [hnorm]; ring
  calc
    ∑ i : I, ‖v i‖ ^ 2 ≤
        ∑ i : I, 3 * (‖mean‖ ^ 2 +
          ‖w • (∑ j : I, delta j)‖ ^ 2 + ‖delta i‖ ^ 2) := by
            exact Finset.sum_le_sum fun i _ => hpointSq i
    _ = 3 * (Fintype.card I : ℝ) * ‖mean‖ ^ 2 +
        3 * ((Fintype.card I : ℝ) *
          ‖w • (∑ j : I, delta j)‖ ^ 2) +
        3 * (∑ i : I, ‖delta i‖ ^ 2) := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          rw [← Finset.mul_sum]
          ring
    _ ≤ 3 * (Fintype.card I : ℝ) * ‖mean‖ ^ 2 +
        3 * (∑ i : I, ‖delta i‖ ^ 2) +
        3 * (∑ i : I, ‖delta i‖ ^ 2) := by
          gcongr
    _ = 6 * (∑ i : I, ‖base - v i‖ ^ 2) +
        3 * (Fintype.card I : ℝ) * ‖w • (∑ i : I, v i)‖ ^ 2 := by
          simp only [delta, mean]
          ring

end

end YangMills.RG
