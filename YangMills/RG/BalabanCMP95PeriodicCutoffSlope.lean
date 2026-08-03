/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP95PeriodicSquareTorusSlope

/-!
# The linear slope of the periodized CMP95 cutoff

PRE-VALIDATION: this source is present, but its `.olean` has not yet been
materialized and its result is not compiler-verified.

The already audited periodic estimate controls the square weight `h^2`.
Using that estimate under a square root would lose half of the physical
scale.  This file instead realizes one periodic cutoff as the Euclidean norm
of the at most two active source translates.  The reverse triangle
inequality then retains the literal `M0^-1` slope needed in CMP99 (3.89).
-/

namespace YangMills.RG

noncomputable section

/-- Nonnegative one-dimensional cutoff belonging to one residue class. -/
def cmp95PeriodicCutoff
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (cell : Fin Q) (t : ℝ) : ℝ :=
  Real.sqrt (cmp95PeriodicSquareWeight P Q cell t)

/-- Physical rescaling of the one-dimensional periodic cutoff. -/
def cmp95RescaledPeriodicCutoff
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (M0 : ℝ) (cell : Fin Q) (t : ℝ) : ℝ :=
  cmp95PeriodicCutoff P Q cell (t / M0)

theorem cmp95PeriodicCutoff_nonneg
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (cell : Fin Q) (t : ℝ) :
    0 ≤ cmp95PeriodicCutoff P Q cell t :=
  Real.sqrt_nonneg _

theorem norm_cmp95PeriodicCutoff_le_one
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (cell : Fin Q) (t : ℝ) :
    ‖cmp95PeriodicCutoff P Q cell t‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (cmp95PeriodicCutoff_nonneg P Q cell t)]
  unfold cmp95PeriodicCutoff
  simpa using Real.sqrt_le_sqrt
    (cmp95PeriodicSquareWeight_le_one P Q cell t)

/-- The periodized cutoff has a linear, rather than square-root, slope.  The
factor two is the square root of the four-point union of the two active
windows at the endpoints. -/
theorem norm_cmp95PeriodicCutoff_sub_le
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (cell : Fin Q) (x y : ℝ) :
    ‖cmp95PeriodicCutoff P Q cell y -
        cmp95PeriodicCutoff P Q cell x‖ ≤
      (2 * P.derivBound) * ‖y - x‖ := by
  classical
  let W := cmp95PeriodicActiveWindow Q cell x ∪
    cmp95PeriodicActiveWindow Q cell y
  let vx : EuclideanSpace ℝ {k // k ∈ W} := WithLp.toLp 2 fun k =>
    P.value (x - ((k.1 * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ))
  let vy : EuclideanSpace ℝ {k // k ∈ W} := WithLp.toLp 2 fun k =>
    P.value (y - ((k.1 * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ))
  have hx : cmp95PeriodicSquareWeight P Q cell x =
      ∑ k ∈ W,
        P.value (x - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) ^ 2 := by
    unfold cmp95PeriodicSquareWeight
    exact tsum_eq_sum fun k hk => by
      by_contra hne
      have hmem := mem_cmp95PeriodicActiveWindow_of_ne_zero
        P Q cell x k hne
      exact hk (Finset.mem_union_left _ hmem)
  have hy : cmp95PeriodicSquareWeight P Q cell y =
      ∑ k ∈ W,
        P.value (y - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) ^ 2 := by
    unfold cmp95PeriodicSquareWeight
    exact tsum_eq_sum fun k hk => by
      by_contra hne
      have hmem := mem_cmp95PeriodicActiveWindow_of_ne_zero
        P Q cell y k hne
      exact hk (Finset.mem_union_right _ hmem)
  have hvx : cmp95PeriodicCutoff P Q cell x = ‖vx‖ := by
    unfold cmp95PeriodicCutoff
    rw [hx, EuclideanSpace.norm_eq]
    congr 1
    rw [← W.sum_attach]
    simp only [Finset.attach_eq_univ, vx, PiLp.toLp_apply,
      Real.norm_eq_abs, sq_abs]
  have hvy : cmp95PeriodicCutoff P Q cell y = ‖vy‖ := by
    unfold cmp95PeriodicCutoff
    rw [hy, EuclideanSpace.norm_eq]
    congr 1
    rw [← W.sum_attach]
    simp only [Finset.attach_eq_univ, vy, PiLp.toLp_apply,
      Real.norm_eq_abs, sq_abs]
  have hcard : W.card ≤ 4 := by
    calc
      W.card ≤
          (cmp95PeriodicActiveWindow Q cell x).card +
            (cmp95PeriodicActiveWindow Q cell y).card := by
        exact Finset.card_union_le _ _
      _ = 4 := by
        rw [card_cmp95PeriodicActiveWindow, card_cmp95PeriodicActiveWindow]
  have hscale : 0 ≤ 2 * P.derivBound * ‖y - x‖ :=
    mul_nonneg (mul_nonneg zero_le_two P.derivBound_nonneg) (norm_nonneg _)
  have hvdiff : ‖vy - vx‖ ≤ 2 * P.derivBound * ‖y - x‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) hscale, EuclideanSpace.norm_sq_eq]
    calc
      ∑ k : {k // k ∈ W}, ‖(vy - vx) k‖ ^ 2 ≤
          ∑ _k : {k // k ∈ W},
            (P.derivBound * ‖y - x‖) ^ 2 := by
        gcongr with k
        have hk := P.norm_value_sub_value_le
          (x - ((k.1 * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ))
          (y - ((k.1 * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ))
        have hk' : ‖(vy - vx) k‖ ≤ P.derivBound * ‖y - x‖ := by
          simpa only [vy, vx, Pi.sub_apply, PiLp.toLp_apply,
            sub_sub_sub_cancel_right] using hk
        exact pow_le_pow_left₀ (norm_nonneg _) hk' 2
      _ = (W.card : ℝ) * (P.derivBound * ‖y - x‖) ^ 2 := by
        rw [Fintype.card_coe]
        simp
      _ ≤ 4 * (P.derivBound * ‖y - x‖) ^ 2 := by
        gcongr
        exact_mod_cast hcard
      _ = (2 * P.derivBound * ‖y - x‖) ^ 2 := by ring
  rw [hvx, hvy, Real.norm_eq_abs]
  exact (abs_norm_sub_norm_le vy vx).trans hvdiff

/-- Physical rescaling retains the exact inverse scale. -/
theorem norm_cmp95RescaledPeriodicCutoff_sub_le
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    {M0 : ℝ} (hM0 : 0 < M0) (cell : Fin Q) (x y : ℝ) :
    ‖cmp95RescaledPeriodicCutoff P Q M0 cell y -
        cmp95RescaledPeriodicCutoff P Q M0 cell x‖ ≤
      ((2 * P.derivBound) / M0) * ‖y - x‖ := by
  have h := norm_cmp95PeriodicCutoff_sub_le
    P Q cell (x / M0) (y / M0)
  unfold cmp95RescaledPeriodicCutoff
  calc
    _ ≤ (2 * P.derivBound) * ‖y / M0 - x / M0‖ := h
    _ = (2 * P.derivBound) * ‖(y - x) / M0‖ := by ring_nf
    _ = ((2 * P.derivBound) / M0) * ‖y - x‖ := by
      rw [norm_div, show ‖M0‖ = M0 by
        simpa [Real.norm_eq_abs] using abs_of_pos hM0]
      ring

end

end YangMills.RG
