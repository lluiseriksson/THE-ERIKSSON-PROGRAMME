/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalPoincareLowModeHodge

/-!
# W-3c — exact block response of the transverse square-wave mode

Fix coarse side `N' = 2` and block length `M`, so the fine side is `2M`.
For distinct bond and modulation directions, the square profile is constant
along each length-`M` line and on each source block.  Consequently the current
`L^{-d}`-normalised block map is computed exactly:

* `squareModeFine_isFluctuation` and `norm_sq_squareModeFine` certify the
  witness in the exact `FinePhysicalOneCochain d M 2 Nc` type;
* `flatBlockConstraintQCLM_squareModeFine_apply_of_ne` gives the pointwise
  coarse field `M · squareSign(1) · w`;
* `norm_sq_flatBlockConstraintQCLM_squareModeFine_of_ne` gives
  `‖QA‖² = 2^d M² ‖w‖²`.

Since `‖A‖² = (2M)^d ‖w‖²`, the block part of the Rayleigh quotient is
exactly `M^(2-d)` for a nonzero mode.  The separate endpoint module assembles
this result with W-3b inside the quotient-gate binder.  No gate conclusion is
asserted in this component module itself.

Oracle target: `[propext, Classical.choice, Quot.sound]`.  No sorry, no axioms.
-/

namespace YangMills.RG

open Matrix Module

noncomputable def squareModeFine (d M Nc : ℕ) [NeZero M]
    (i j : Fin d) (w : SUNLieCoord Nc) :
    FinePhysicalOneCochain d M 2 Nc :=
  squareModeCochain d M Nc i j w

@[simp] theorem squareModeFine_apply (d M Nc : ℕ) [NeZero M]
    (i j : Fin d) (w : SUNLieCoord Nc) (b : PhysicalBond d (M * 2)) :
    squareModeFine d M Nc i j w b =
      if b.2 = i then
        (if (b.1 j).val < M then 1 else -1 : ℝ) • w
      else 0 := by
  rfl

private theorem fineLineSum_squareModeFine_of_ne
    (d M Nc : ℕ) [NeZero M] (i j : Fin d) (hij : i ≠ j)
    (w : SUNLieCoord Nc) (x : FinBox d (M * 2)) :
    fineLineSum M 2
        (fun e : ConcreteEdge d (M * 2) =>
          squareModeFine d M Nc i j w (physicalBondOfEdge e)) i x
      = (M : ℝ) •
          ((if (x j).val < M then 1 else -1 : ℝ) • w) := by
  rw [fineLineSum]
  have hshift : ∀ k : ℕ,
      (((fun y : FinBox d (M * 2) => FinBox.shift y i)^[k] x) j) = x j := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [Function.iterate_succ_apply', FinBox.shift, if_neg hij.symm, ih]
  have hterm : ∀ k ∈ Finset.range M,
      squareModeFine d M Nc i j w
          (physicalBondOfEdge
            (ConcreteEdge.mk
              ((fun y : FinBox d (M * 2) => FinBox.shift y i)^[k] x)
              i true)) =
        (if (x j).val < M then 1 else -1 : ℝ) • w := by
    intro k _
    rw [physicalBondOfEdge_mk_true, squareModeFine_apply, if_pos rfl]
    change (if
        ((((fun y : FinBox d (M * 2) => FinBox.shift y i)^[k] x) j).val < M)
      then 1 else -1 : ℝ) • w = _
    rw [hshift k]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range]
  exact (Nat.cast_smul_eq_nsmul ℝ M
    ((if (x j).val < M then 1 else -1 : ℝ) • w)).symm

private theorem squareSign_fine_eq_coarse_of_mem_block
    (d M : ℕ) [NeZero M] (j : Fin d) (y : FinBox d 2)
    (x : FinBox d (M * 2)) (hx : x ∈ blockOf M 2 y) :
    (if (x j).val < M then 1 else -1 : ℝ) = squareSign 1 (y j) := by
  have hcube := (blockSite_eq_iff_cube M 2 x y).mp
    ((mem_blockOf M 2 y x).mp hx)
  have hy := (y j).isLt
  by_cases hy0 : (y j).val = 0
  · have hxlt : (x j).val < M := by
      have hj := (hcube j).2
      simpa [hy0] using hj
    simp [squareSign, hy0, hxlt]
  · have hy1 : (y j).val = 1 := by omega
    have hxge : ¬(x j).val < M := by
      have hj := (hcube j).1
      simp [hy1] at hj
      omega
    simp [squareSign, hy1, hxge]

theorem flatBlockConstraintQCLM_squareModeFine_apply_of_ne
    (d M Nc : ℕ) [NeZero M] (i j : Fin d) (hij : i ≠ j)
    (w : SUNLieCoord Nc) (b : PhysicalBond d 2) :
    flatBlockConstraintQCLM (d := d) (Nc := Nc) M 2
        (squareModeFine d M Nc i j w) b =
      if b.2 = i then
        (M : ℝ) • (squareSign 1 (b.1 j) • w)
      else 0 := by
  rw [flatBlockConstraintQCLM_apply]
  by_cases hb : b.2 = i
  · rw [if_pos hb]
    subst i
    rw [linAvg]
    have hterm : ∀ x ∈ blockOf M 2 b.1,
        fineLineSum M 2
            (fun e : ConcreteEdge d (M * 2) =>
              squareModeFine d M Nc b.2 j w (physicalBondOfEdge e))
            b.2 x =
          (M : ℝ) • (squareSign 1 (b.1 j) • w) := by
      intro x hx
      rw [fineLineSum_squareModeFine_of_ne d M Nc b.2 j hij w x,
        squareSign_fine_eq_coarse_of_mem_block d M j b.1 x hx]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, blockOf_card]
    have hcast : (M ^ d) • ((M : ℝ) • (squareSign 1 (b.1 j) • w)) =
        (((M ^ d : ℕ) : ℝ) •
          ((M : ℝ) • (squareSign 1 (b.1 j) • w))) :=
      (Nat.cast_smul_eq_nsmul ℝ (M ^ d)
        ((M : ℝ) • (squareSign 1 (b.1 j) • w))).symm
    rw [hcast, Nat.cast_pow, smul_smul]
    have hpow : (M : ℝ) ^ d ≠ 0 := pow_ne_zero d (by exact_mod_cast NeZero.ne M)
    rw [inv_mul_cancel₀ hpow, one_smul]
  · rw [if_neg hb]
    simp [linAvg, fineLineSum, squareModeFine_apply, hb]

theorem norm_sq_flatBlockConstraintQCLM_squareModeFine_of_ne
    (d M Nc : ℕ) [NeZero M] (i j : Fin d) (hij : i ≠ j)
    (w : SUNLieCoord Nc) :
    ‖flatBlockConstraintQCLM (d := d) (Nc := Nc) M 2
        (squareModeFine d M Nc i j w)‖ ^ 2 =
      (2 : ℝ) ^ d * (M : ℝ) ^ 2 * ‖w‖ ^ 2 := by
  classical
  rw [PiLp.norm_sq_eq_of_L2]
  have hterm : ∀ b : PhysicalBond d 2,
      ‖flatBlockConstraintQCLM (d := d) (Nc := Nc) M 2
          (squareModeFine d M Nc i j w) b‖ ^ 2 =
        if b.2 = i then (M : ℝ) ^ 2 * ‖w‖ ^ 2 else 0 := by
    intro b
    rw [flatBlockConstraintQCLM_squareModeFine_apply_of_ne d M Nc i j hij w b]
    by_cases hb : b.2 = i
    · rw [if_pos hb, if_pos hb, norm_smul, norm_smul, mul_pow, mul_pow,
        Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
        squareSign_sq]
      ring
    · rw [if_neg hb, if_neg hb, norm_zero]
      norm_num
  rw [Finset.sum_congr rfl (fun b _ => hterm b), Fintype.sum_prod_type]
  have hinner : ∀ _x : FinBox d 2,
      (∑ k : Fin d, if k = i then (M : ℝ) ^ 2 * ‖w‖ ^ 2 else 0) =
        (M : ℝ) ^ 2 * ‖w‖ ^ 2 :=
    fun _x =>
      (Finset.sum_ite_eq' Finset.univ i
        (fun _ => (M : ℝ) ^ 2 * ‖w‖ ^ 2)).trans
      (if_pos (Finset.mem_univ i))
  rw [Finset.sum_congr rfl (fun x _ => hinner x), Finset.sum_const,
    Finset.card_univ, card_finBox, nsmul_eq_mul]
  push_cast
  ring

private theorem sum_squareSign_mul_two (M : ℕ) :
    ∑ m : Fin (M * 2), (if m.val < M then 1 else -1 : ℝ) = 0 := by
  simpa [squareSign] using sum_squareSign M

private theorem sum_finBox_squareSign_mul_two
    (d M : ℕ) (j : Fin d) :
    ∑ x : FinBox d (M * 2),
      (if (x j).val < M then 1 else -1 : ℝ) = 0 := by
  classical
  have hsplit :
      ∑ x : FinBox d (M * 2),
          (if (x j).val < M then 1 else -1 : ℝ) =
        ∑ p : Fin (M * 2) × ({k : Fin d // k ≠ j} → Fin (M * 2)),
          (if p.1.val < M then 1 else -1 : ℝ) := by
    rw [← Equiv.sum_comp
      (Equiv.piSplitAt j (fun _ : Fin d => Fin (M * 2)))
      (fun p => (if p.1.val < M then 1 else -1 : ℝ))]
    rfl
  rw [hsplit, Fintype.sum_prod_type]
  have hinner : ∀ m : Fin (M * 2),
      (∑ _r : ({k : Fin d // k ≠ j} → Fin (M * 2)),
        (if m.val < M then 1 else -1 : ℝ)) =
      Fintype.card ({k : Fin d // k ≠ j} → Fin (M * 2)) •
        (if m.val < M then 1 else -1 : ℝ) := by
    intro m
    rw [Finset.sum_const, Finset.card_univ]
  rw [Finset.sum_congr rfl (fun m _ => hinner m)]
  rw [← Finset.smul_sum, sum_squareSign_mul_two, smul_zero]

theorem squareModeFine_isFluctuation (d M Nc : ℕ) [NeZero M]
    (i j : Fin d) (w : SUNLieCoord Nc) :
    IsFluctuationCochain (squareModeFine d M Nc i j w) := by
  classical
  intro v
  rw [PiLp.inner_apply]
  have hterm : ∀ b : PhysicalBond d (M * 2),
      (inner ℝ
        (constantPhysicalGaugeOneCochain
          (d := d) (N := M * 2) (Nc := Nc) v b)
        (squareModeFine d M Nc i j w b) : ℝ) =
        if b.2 = i then
          (if (b.1 j).val < M then 1 else -1 : ℝ) *
            (inner ℝ (v i) w : ℝ)
        else 0 := by
    intro b
    rw [constantPhysicalGaugeOneCochain_apply, squareModeFine_apply]
    by_cases hb : b.2 = i
    · rw [if_pos hb, if_pos hb, hb, real_inner_smul_right]
    · rw [if_neg hb, if_neg hb, inner_zero_right]
  rw [Finset.sum_congr rfl (fun b _ => hterm b), Fintype.sum_prod_type]
  have hinner : ∀ x : FinBox d (M * 2),
      (∑ k : Fin d, if k = i then
          (if (x j).val < M then 1 else -1 : ℝ) *
            (inner ℝ (v i) w : ℝ)
        else 0) =
      (if (x j).val < M then 1 else -1 : ℝ) *
        (inner ℝ (v i) w : ℝ) :=
    fun x => Finset.sum_ite_eq' Finset.univ i
      (fun _ => (if (x j).val < M then 1 else -1 : ℝ) *
        (inner ℝ (v i) w : ℝ)) |>.trans
      (if_pos (Finset.mem_univ i))
  rw [Finset.sum_congr rfl (fun x _ => hinner x), ← Finset.sum_mul,
    sum_finBox_squareSign_mul_two, zero_mul]

theorem norm_sq_squareModeFine (d M Nc : ℕ) [NeZero M]
    (i j : Fin d) (w : SUNLieCoord Nc) :
    ‖squareModeFine d M Nc i j w‖ ^ 2 =
      ((M * 2 : ℕ) : ℝ) ^ d * ‖w‖ ^ 2 := by
  classical
  rw [PiLp.norm_sq_eq_of_L2]
  have hterm : ∀ b : PhysicalBond d (M * 2),
      ‖squareModeFine d M Nc i j w b‖ ^ 2 =
        if b.2 = i then ‖w‖ ^ 2 else 0 := by
    intro b
    rw [squareModeFine_apply]
    by_cases hb : b.2 = i
    · rw [if_pos hb, if_pos hb, norm_smul, mul_pow, Real.norm_eq_abs,
        sq_abs]
      split <;> norm_num
    · rw [if_neg hb, if_neg hb, norm_zero]
      norm_num
  rw [Finset.sum_congr rfl (fun b _ => hterm b), Fintype.sum_prod_type]
  have hinner : ∀ _x : FinBox d (M * 2),
      (∑ k : Fin d, if k = i then ‖w‖ ^ 2 else 0) = ‖w‖ ^ 2 :=
    fun _x => (Finset.sum_ite_eq' Finset.univ i (fun _ => ‖w‖ ^ 2)).trans
      (if_pos (Finset.mem_univ i))
  rw [Finset.sum_congr rfl (fun x _ => hinner x), Finset.sum_const,
    Finset.card_univ, card_finBox, nsmul_eq_mul]
  push_cast
  ring

end YangMills.RG
