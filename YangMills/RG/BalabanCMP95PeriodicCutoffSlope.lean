/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP95PeriodicSquareTorusSlope
import YangMills.RG.BlockBasepointDistance

/-!
# The linear slope of the periodized CMP95 cutoff

Compiler-verified at source checkpoint
`837040284f5ce1d358d42eb8f6c01689829db29b` in durable GitHub Actions run
`30971247380`.  The focal completed 8,494 jobs and all eight audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`.

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
        exact hk'
      _ = (W.card : ℝ) * (P.derivBound * ‖y - x‖) ^ 2 := by
        simp [Fintype.card_coe]
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

/-- The rescaled cutoff has the literal physical period `M0 * Q`. -/
theorem cmp95RescaledPeriodicCutoff_add_period
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (M0 : ℝ) (hM0 : M0 ≠ 0) (cell : Fin Q) (t : ℝ) :
    cmp95RescaledPeriodicCutoff P Q M0 cell (t + M0 * Q) =
      cmp95RescaledPeriodicCutoff P Q M0 cell t := by
  unfold cmp95RescaledPeriodicCutoff
  rw [show (t + M0 * Q) / M0 = t / M0 + Q by field_simp]
  unfold cmp95PeriodicCutoff
  rw [cmp95PeriodicSquareWeight_add_period]

/-- The tensor cutoff is the product of its nonnegative one-dimensional
cutoffs.  This avoids differentiating a square root at zero. -/
theorem cmp95RescaledPeriodicTensorCutoff_eq_prod
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (M0 : ℝ) (cell : FinBox 4 Q) (x : Fin 4 → ℝ) :
    cmp95RescaledPeriodicTensorCutoff P Q M0 cell x =
      ∏ i, cmp95RescaledPeriodicCutoff P Q M0 (cell i) (x i) := by
  classical
  unfold cmp95RescaledPeriodicTensorCutoff
    cmp95RescaledPeriodicTensorSquareWeight
  have hsqrt :
      Real.sqrt
          (∏ i : Fin 4,
            cmp95RescaledPeriodicSquareWeight P Q M0 (cell i) (x i)) =
        ∏ i : Fin 4,
          Real.sqrt
            (cmp95RescaledPeriodicSquareWeight P Q M0 (cell i) (x i)) := by
    simpa using Real.sqrt_prod (Finset.univ : Finset (Fin 4))
      (fun i _ => cmp95RescaledPeriodicSquareWeight_nonneg
        P Q M0 (cell i) (x i))
  rw [hsqrt]
  apply Finset.prod_congr rfl
  intro i _hi
  rfl

/-- Boundary-safe tensor cutoff slope on the physical four-torus.  The
constant `8` is `4` coordinates times the one-dimensional constant `2`; no
new overlap parameter is introduced. -/
theorem norm_cmp95RescaledPeriodicTensorCutoff_finBox_sub_le
    (P : CMP95SourceSmoothPartitionProfile)
    (M0 Q : ℕ) [NeZero M0] [NeZero Q]
    (cell : FinBox 4 Q) (offset : Fin 4 → ℝ)
    (x y : FinBox 4 (M0 * Q)) :
    ‖cmp95RescaledPeriodicTensorCutoff P Q M0 cell
          (fun i => (y i).val + offset i) -
        cmp95RescaledPeriodicTensorCutoff P Q M0 cell
          (fun i => (x i).val + offset i)‖ ≤
      ((8 * P.derivBound) / M0) * (finBoxDist x y : ℝ) := by
  classical
  rw [cmp95RescaledPeriodicTensorCutoff_eq_prod,
    cmp95RescaledPeriodicTensorCutoff_eq_prod]
  calc
    ‖∏ i, cmp95RescaledPeriodicCutoff P Q M0 (cell i)
          ((y i).val + offset i) -
        ∏ i, cmp95RescaledPeriodicCutoff P Q M0 (cell i)
          ((x i).val + offset i)‖ ≤
      ∑ i, ‖cmp95RescaledPeriodicCutoff P Q M0 (cell i)
          ((y i).val + offset i) -
        cmp95RescaledPeriodicCutoff P Q M0 (cell i)
          ((x i).val + offset i)‖ := by
      apply CMP95SourceSmoothPartitionProfile.norm_prod_sub_prod_le_sum_norm_sub
        Finset.univ
      · intro i _
        exact norm_cmp95PeriodicCutoff_le_one P Q (cell i)
          (((y i).val + offset i) / M0)
      · intro i _
        exact norm_cmp95PeriodicCutoff_le_one P Q (cell i)
          (((x i).val + offset i) / M0)
    _ ≤ ∑ _i : Fin 4,
        ((2 * P.derivBound) / M0) * (finBoxDist x y : ℝ) := by
      gcongr with i
      let f : ℝ → ℝ := fun t =>
        cmp95RescaledPeriodicCutoff P Q M0 (cell i) (t + offset i)
      have hi : ‖f (y i).val - f (x i).val‖ ≤
          ((2 * P.derivBound) / M0) *
            (finTorusDist (x i) (y i) : ℝ) := by
        apply norm_periodic_fin_value_sub_le_finTorusDist
        · exact div_nonneg (mul_nonneg (by norm_num) P.derivBound_nonneg)
            (Nat.cast_nonneg M0)
        · intro t
          dsimp [f]
          rw [show t + (M0 * Q : ℕ) + offset i =
              (t + offset i) + (M0 : ℝ) * Q by push_cast; ring]
          exact cmp95RescaledPeriodicCutoff_add_period
            P Q M0 (by exact_mod_cast NeZero.ne M0) (cell i) (t + offset i)
        · intro u v
          dsimp [f]
          simpa only [add_sub_add_right_eq_sub] using
            norm_cmp95RescaledPeriodicCutoff_sub_le P Q
              (by exact_mod_cast NeZero.pos M0) (cell i)
              (u + offset i) (v + offset i)
      exact hi.trans
        (mul_le_mul_of_nonneg_left
          (Nat.cast_le.2 (finTorusDist_le_finBoxDist x y i))
          (div_nonneg (mul_nonneg (by norm_num) P.derivBound_nonneg)
            (Nat.cast_nonneg M0)))
    _ = ((8 * P.derivBound) / M0) * (finBoxDist x y : ℝ) := by
      simp
      ring

/-- Boundary-safe slope of the auxiliary generated fine-lattice cutoff.
The inverse translation spacing is retained exactly, but this spacing is only
twice the certified terminal precision range.  Therefore this theorem alone
does not provide the source `M⁻¹` gain in CMP99 (3.89). -/
theorem norm_cmp99SourceGeneratedFineCellCutoff_finBox_sub_le
    (P : CMP95SourceSmoothPartitionProfile)
    (M Q depth : ℕ) [NeZero M] [NeZero Q]
    (cell : FinBox 4 Q)
    (x y : FinBox 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1))) :
    ‖cmp99SourceGeneratedFineCellCutoff P M Q depth cell y -
        cmp99SourceGeneratedFineCellCutoff P M Q depth cell x‖ ≤
      ((8 * P.derivBound) /
        cmp99SourceGeneratedCellCutoffScale M depth) *
        (finBoxDist x y : ℝ) := by
  classical
  let M0 := 2 * M ^ (depth + 1)
  letI : NeZero M0 :=
    ⟨Nat.mul_ne_zero (by omega) (pow_ne_zero _ (NeZero.ne M))⟩
  let offset : Fin 4 → ℝ := fun _ =>
    1 / 2 - cmp99SourceGeneratedCellCutoffScale M depth / 2
  let hsize : cmp99RegionalLatticeSize M (2 * Q) (depth + 1) = M0 * Q :=
    (cmp99SourceGeneratedCellCutoffScale_mul_Q M Q depth).symm
  let x' : FinBox 4 (M0 * Q) := hsize ▸ x
  let y' : FinBox 4 (M0 * Q) := hsize ▸ y
  have hxval (i : Fin 4) : (x' i).val = (x i).val := by
    exact finBox_cast_apply_val hsize x i
  have hyval (i : Fin 4) : (y' i).val = (y i).val := by
    exact finBox_cast_apply_val hsize y i
  have hdist : finBoxDist x' y' = finBoxDist x y := by
    exact finBoxDist_cast_size hsize x y
  have hxcoord :
      (fun i => ((x' i).val : ℝ) + offset i) =
        cmp99SourceGeneratedFineCellCoordinate M depth
          (fun i => (x i).val) := by
    funext i
    simp only [offset, cmp99SourceGeneratedFineCellCoordinate, hxval]
    ring
  have hycoord :
      (fun i => ((y' i).val : ℝ) + offset i) =
        cmp99SourceGeneratedFineCellCoordinate M depth
          (fun i => (y i).val) := by
    funext i
    simp only [offset, cmp99SourceGeneratedFineCellCoordinate, hyval]
    ring
  have h := norm_cmp95RescaledPeriodicTensorCutoff_finBox_sub_le
    P M0 Q cell offset x' y'
  rw [hxcoord, hycoord] at h
  simpa [cmp99SourceGeneratedFineCellCutoff,
    cmp99SourceGeneratedCellCutoffScale, M0, hdist] using h

end

end YangMills.RG
