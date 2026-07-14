/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalPoincareLowModeFalsifier

/-!
# W-3b — exact Hodge energy of the square-wave low mode

This module evaluates both first-order pieces of the flat gauge Hodge form on
the explicit W-3a mode.  The square profile has exactly two jump walls, so the
finite-volume calculation is exact:

* `norm_sq_gaugeConstraint_squareMode`: the divergence energy is
  `8 · (2M)^(d-1) · ‖w‖²` when the bond and modulation directions coincide,
  and zero otherwise;
* `norm_sq_covariantD1_squareMode`: the curl energy has the complementary
  dichotomy;
* `flatGaugeHodgeK0_squareMode_energy`: their sum is always
  `8 · (2M)^(d-1) · ‖w‖²`.

Together with W-3a's exact norm `(2M)^d · ‖w‖²`, this isolates the Hodge
Rayleigh scaling `8/(2M) = 4/M`.  It does not evaluate the block response
`‖Q A‖²`; that remains precisely the W-3c obligation.  No Poincaré-gate or
mass-gap conclusion is asserted here.

Oracle target: `[propext, Classical.choice, Quot.sound]`.  No sorry, no axioms.
-/

namespace YangMills.RG

open Matrix Module

private def circleShift (M : ℕ) [NeZero M] (m : Fin (M * 2)) : Fin (M * 2) :=
  ⟨(m.val + 1) % (M * 2), Nat.mod_lt _ (by have := NeZero.ne M; omega)⟩

private theorem squareSign_circleShift_diff_sq (M : ℕ) [NeZero M]
    (m : Fin (M * 2)) :
    (squareSign M (circleShift M m) - squareSign M m) ^ 2
      = if m.val + 1 = M ∨ m.val + 1 = M * 2 then 4 else 0 := by
  have hm := m.isLt
  have hM : 0 < M := NeZero.pos M
  by_cases hwrap : m.val + 1 = M * 2
  · have hbase : ¬m.val < M := by omega
    simp [circleShift, squareSign, hwrap, hbase, hM]
    all_goals norm_num
  · have hlt : m.val + 1 < M * 2 := by omega
    have hmod : (m.val + 1) % (M * 2) = m.val + 1 :=
      Nat.mod_eq_of_lt hlt
    by_cases hjump : m.val + 1 = M
    · have hbase : m.val < M := by omega
      have hMmod : M % (M * 2) = M := Nat.mod_eq_of_lt (by omega)
      simp [circleShift, squareSign, hjump, hbase, hMmod]
      all_goals norm_num
    · by_cases hbase : m.val < M
      · have hshift : m.val + 1 < M := by omega
        simp [circleShift, squareSign, hmod, hshift, hbase, hjump, hwrap]
      · have hshift : ¬m.val + 1 < M := by omega
        simp [circleShift, squareSign, hmod, hshift, hbase, hjump, hwrap]

private theorem sum_squareSign_circleShift_diff_sq (M : ℕ) [NeZero M] :
    ∑ m : Fin (M * 2),
        (squareSign M (circleShift M m) - squareSign M m) ^ 2 = 8 := by
  rw [Finset.sum_congr rfl (fun m _ => squareSign_circleShift_diff_sq M m)]
  simp only [Finset.sum_ite]
  let a : Fin (M * 2) := ⟨M - 1, by have := NeZero.pos M; omega⟩
  let b : Fin (M * 2) := ⟨M * 2 - 1, by have := NeZero.pos M; omega⟩
  have hab : a ≠ b := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [a, b] at hv
    have := NeZero.pos M
    omega
  have hfilter :
      Finset.univ.filter (fun m : Fin (M * 2) =>
        m.val + 1 = M ∨ m.val + 1 = M * 2) = {a, b} := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · left
        apply Fin.ext
        dsimp [a]
        have := NeZero.pos M
        omega
      · right
        apply Fin.ext
        dsimp [b]
        have := NeZero.pos M
        omega
    · rintro (rfl | rfl)
      · left
        dsimp [a]
        have := NeZero.pos M
        omega
      · right
        dsimp [b]
        have := NeZero.pos M
        omega
  rw [hfilter]
  simp [hab]
  norm_num

private theorem card_fin_ne (d : ℕ) (j : Fin d) :
    Fintype.card {k : Fin d // k ≠ j} = d - 1 := by
  rw [Fintype.card_subtype_compl (fun k : Fin d => k = j)]
  simp

private theorem sum_finBox_squareSign_circleShift_diff_sq
    (d M : ℕ) [NeZero M] (j : Fin d) :
    ∑ x : FinBox d (M * 2),
        (squareSign M (circleShift M (x j)) - squareSign M (x j)) ^ 2
      = 8 * ((M * 2 : ℕ) : ℝ) ^ (d - 1) := by
  classical
  have hsplit :
      ∑ x : FinBox d (M * 2),
          (squareSign M (circleShift M (x j)) - squareSign M (x j)) ^ 2
        = ∑ p : Fin (M * 2) × ({k : Fin d // k ≠ j} → Fin (M * 2)),
            (squareSign M (circleShift M p.1) - squareSign M p.1) ^ 2 := by
    rw [← Equiv.sum_comp
      (Equiv.piSplitAt j (fun _ : Fin d => Fin (M * 2)))
      (fun p =>
        (squareSign M (circleShift M p.1) - squareSign M p.1) ^ 2)]
    rfl
  rw [hsplit, Fintype.sum_prod_type]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.mul_sum, sum_squareSign_circleShift_diff_sq]
  rw [Finset.card_univ, Fintype.card_fun, card_fin_ne d j, Fintype.card_fin]
  push_cast
  ring

private theorem shift_apply_self_eq_circleShift
    {d M : ℕ} [NeZero M] (x : FinBox d (M * 2)) (j : Fin d) :
    (x.shift j) j = circleShift M (x j) := by
  apply Fin.ext
  simp [FinBox.shift, circleShift]

private theorem sum_finBox_squareSign_shiftBack_diff_sq
    (d M : ℕ) [NeZero M] (j : Fin d) :
    ∑ x : FinBox d (M * 2),
        (squareSign M (x j) - squareSign M ((x.shiftBack j) j)) ^ 2
      = 8 * ((M * 2 : ℕ) : ℝ) ^ (d - 1) := by
  let F : FinBox d (M * 2) → ℝ := fun x =>
    (squareSign M (x j) - squareSign M ((x.shiftBack j) j)) ^ 2
  have hshift := FinBox.sum_shift F j
  have hpoint : ∀ x : FinBox d (M * 2),
      F (x.shift j) =
        (squareSign M (circleShift M (x j)) - squareSign M (x j)) ^ 2 := by
    intro x
    simp only [F, FinBox.shiftBack_shift]
    rw [shift_apply_self_eq_circleShift]
  rw [Finset.sum_congr rfl (fun x _ => hpoint x)] at hshift
  rw [← hshift]
  exact sum_finBox_squareSign_circleShift_diff_sq d M j

theorem gaugeConstraint_squareMode_apply
    (d M Nc : ℕ) [NeZero d] [NeZero M] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (i j : Fin d) (w : SUNLieCoord Nc)
    (x : FinBox d (M * 2)) :
    gaugeConstraintQCLM ρ
        (trivialPhysicalGaugeBackground d (M * 2) Nc)
        (squareModeCochain d M Nc i j w) x
      = if i = j then
          (squareSign M (x j) - squareSign M ((x.shiftBack j) j)) • w
        else 0 := by
  classical
  rw [gaugeConstraintQCLM_trivial_apply]
  have hterm : ∀ k : Fin d,
      (squareModeCochain d M Nc i j w (x, k) -
        squareModeCochain d M Nc i j w (x.shiftBack k, k))
        = if k = i then
            (squareSign M (x j) -
              squareSign M ((x.shiftBack i) j)) • w
          else 0 := by
    intro k
    by_cases hki : k = i
    · subst k
      simp [squareModeCochain_apply, sub_smul]
    · simp [squareModeCochain_apply, hki]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  rw [Finset.sum_ite_eq' Finset.univ i]
  simp only [Finset.mem_univ, if_true]
  by_cases hij : i = j
  · subst i
    simp
  · have hji : j ≠ i := Ne.symm hij
    simp [hij, FinBox.shiftBack, hji]

theorem norm_sq_gaugeConstraint_squareMode
    (d M Nc : ℕ) [NeZero d] [NeZero M] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (i j : Fin d) (w : SUNLieCoord Nc) :
    ‖gaugeConstraintQCLM ρ
        (trivialPhysicalGaugeBackground d (M * 2) Nc)
        (squareModeCochain d M Nc i j w)‖ ^ 2
      = if i = j then
          8 * ((M * 2 : ℕ) : ℝ) ^ (d - 1) * ‖w‖ ^ 2
        else 0 := by
  classical
  rw [PiLp.norm_sq_eq_of_L2]
  by_cases hij : i = j
  · subst i
    simp only [if_pos]
    have hterm : ∀ x : FinBox d (M * 2),
        ‖gaugeConstraintQCLM ρ
            (trivialPhysicalGaugeBackground d (M * 2) Nc)
            (squareModeCochain d M Nc j j w) x‖ ^ 2
          = (squareSign M (x j) -
              squareSign M ((x.shiftBack j) j)) ^ 2 * ‖w‖ ^ 2 := by
      intro x
      rw [gaugeConstraint_squareMode_apply]
      simp only [if_pos]
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [Finset.sum_congr rfl (fun x _ => hterm x)]
    rw [← Finset.sum_mul, sum_finBox_squareSign_shiftBack_diff_sq]
  · simp [gaugeConstraint_squareMode_apply, hij]

theorem covariantD1_squareMode_apply
    (d M Nc : ℕ) [NeZero d] [NeZero M] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (i j : Fin d) (w : SUNLieCoord Nc)
    (p : ConcretePlaquette d (M * 2)) :
    covariantD1CLM ρ (trivialPhysicalGaugeBackground d (M * 2) Nc)
        (squareModeCochain d M Nc i j w) p
      = if p.dir1 = i then
          (squareSign M (p.site j) -
            squareSign M ((p.site.shift p.dir2) j)) • w
        else if p.dir2 = i then
          (squareSign M ((p.site.shift p.dir1) j) -
            squareSign M (p.site j)) • w
        else 0 := by
  rw [covariantD1CLM_trivial_apply]
  have h12 : p.dir1 ≠ p.dir2 := ne_of_lt p.hlt
  by_cases h1 : p.dir1 = i
  · have h2 : p.dir2 ≠ i := by
      intro h
      exact h12 (h1.trans h.symm)
    simp [squareModeCochain_apply, h1, h2, sub_smul]
  · by_cases h2 : p.dir2 = i
    · simp [squareModeCochain_apply, h1, h2, sub_smul]
    · simp [squareModeCochain_apply, h1, h2]

private theorem norm_sq_covariantD1_squareMode_apply
    (d M Nc : ℕ) [NeZero d] [NeZero M] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (i j : Fin d) (w : SUNLieCoord Nc)
    (p : ConcretePlaquette d (M * 2)) :
    ‖covariantD1CLM ρ (trivialPhysicalGaugeBackground d (M * 2) Nc)
        (squareModeCochain d M Nc i j w) p‖ ^ 2
      = if (p.dir1 = i ∧ p.dir2 = j) ∨ (p.dir1 = j ∧ p.dir2 = i) then
          (squareSign M (circleShift M (p.site j)) -
            squareSign M (p.site j)) ^ 2 * ‖w‖ ^ 2
        else 0 := by
  rw [covariantD1_squareMode_apply]
  have h12 : p.dir1 ≠ p.dir2 := ne_of_lt p.hlt
  by_cases h1 : p.dir1 = i
  · have h2 : p.dir2 ≠ i := by
      intro h
      exact h12 (h1.trans h.symm)
    rw [if_pos h1]
    by_cases hj2 : j = p.dir2
    · subst j
      have hcond :
          (p.dir1 = i ∧ p.dir2 = p.dir2) ∨
            (p.dir1 = p.dir2 ∧ p.dir2 = i) := Or.inl ⟨h1, rfl⟩
      rw [if_pos hcond, shift_apply_self_eq_circleShift]
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    · have hcond : ¬((p.dir1 = i ∧ p.dir2 = j) ∨
          (p.dir1 = j ∧ p.dir2 = i)) := by
        rintro (h | h)
        · exact hj2 h.2.symm
        · exact h2 h.2
      rw [if_neg hcond]
      have hshift : (p.site.shift p.dir2) j = p.site j := by
        simp [FinBox.shift, hj2]
      rw [hshift, sub_self, zero_smul, norm_zero]
      norm_num
  · by_cases h2 : p.dir2 = i
    · rw [if_neg h1, if_pos h2]
      by_cases hj1 : j = p.dir1
      · subst j
        have hcond :
            (p.dir1 = i ∧ p.dir2 = p.dir1) ∨
              (p.dir1 = p.dir1 ∧ p.dir2 = i) := Or.inr ⟨rfl, h2⟩
        rw [if_pos hcond, shift_apply_self_eq_circleShift]
        rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      · have hcond : ¬((p.dir1 = i ∧ p.dir2 = j) ∨
            (p.dir1 = j ∧ p.dir2 = i)) := by
          rintro (h | h)
          · exact h1 h.1
          · exact hj1 h.1.symm
        rw [if_neg hcond]
        have hshift : (p.site.shift p.dir1) j = p.site j := by
          simp [FinBox.shift, hj1]
        rw [hshift, sub_self, zero_smul, norm_zero]
        norm_num
    · rw [if_neg h1, if_neg h2]
      have hcond : ¬((p.dir1 = i ∧ p.dir2 = j) ∨
          (p.dir1 = j ∧ p.dir2 = i)) := by
        rintro (h | h)
        · exact h1 h.1
        · exact h2 h.2
      rw [if_neg hcond, norm_zero]
      norm_num

private abbrev OrderedDirPair (d : ℕ) :=
  {q : Fin d × Fin d // q.1 < q.2}

private def concretePlaquetteEquiv (d N : ℕ) :
    ConcretePlaquette d N ≃ FinBox d N × OrderedDirPair d where
  toFun p := (p.site, ⟨(p.dir1, p.dir2), p.hlt⟩)
  invFun p := ⟨p.1, p.2.1.1, p.2.1.2, p.2.2⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p with | mk site dirs => cases dirs; rfl

theorem norm_sq_covariantD1_squareMode
    (d M Nc : ℕ) [NeZero d] [NeZero M] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (i j : Fin d) (w : SUNLieCoord Nc) :
    ‖covariantD1CLM ρ (trivialPhysicalGaugeBackground d (M * 2) Nc)
        (squareModeCochain d M Nc i j w)‖ ^ 2
      = if i = j then 0
        else 8 * ((M * 2 : ℕ) : ℝ) ^ (d - 1) * ‖w‖ ^ 2 := by
  classical
  rw [PiLp.norm_sq_eq_of_L2]
  by_cases hij : i = j
  · subst i
    simp only [if_pos]
    apply Finset.sum_eq_zero
    intro p _
    rw [norm_sq_covariantD1_squareMode_apply]
    have h12 : p.dir1 ≠ p.dir2 := ne_of_lt p.hlt
    have hcond : ¬((p.dir1 = j ∧ p.dir2 = j) ∨
        (p.dir1 = j ∧ p.dir2 = j)) := by
      rintro (h | h) <;> exact h12 (h.1.trans h.2.symm)
    rw [if_neg hcond]
  · simp only [if_neg hij]
    rw [← Equiv.sum_comp (concretePlaquetteEquiv d (M * 2)).symm
      (fun p =>
        ‖covariantD1CLM ρ
          (trivialPhysicalGaugeBackground d (M * 2) Nc)
          (squareModeCochain d M Nc i j w) p‖ ^ 2)]
    rw [Fintype.sum_prod_type]
    by_cases hlt : i < j
    · let target : OrderedDirPair d := ⟨(i, j), hlt⟩
      have hfilter :
          Finset.univ.filter (fun q : OrderedDirPair d =>
            (q.1.1 = i ∧ q.1.2 = j) ∨
              (q.1.1 = j ∧ q.1.2 = i)) = {target} := by
        ext q
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton]
        constructor
        · rintro (h | h)
          · apply Subtype.ext
            rcases h with ⟨h1, h2⟩
            apply Prod.ext <;> assumption
          · have hq := q.2
            rcases h with ⟨h1, h2⟩
            rw [h1, h2] at hq
            omega
        · rintro rfl
          exact Or.inl ⟨rfl, rfl⟩
      have hinner : ∀ x : FinBox d (M * 2),
          (∑ q : OrderedDirPair d,
            ‖covariantD1CLM ρ
                (trivialPhysicalGaugeBackground d (M * 2) Nc)
                (squareModeCochain d M Nc i j w)
                ((concretePlaquetteEquiv d (M * 2)).symm (x, q))‖ ^ 2)
            = (squareSign M (circleShift M (x j)) -
                squareSign M (x j)) ^ 2 * ‖w‖ ^ 2 := by
        intro x
        rw [Finset.sum_congr rfl (fun q _ =>
          norm_sq_covariantD1_squareMode_apply d M Nc ρ i j w
            ((concretePlaquetteEquiv d (M * 2)).symm (x, q)))]
        change (∑ q : OrderedDirPair d,
          if (q.1.1 = i ∧ q.1.2 = j) ∨ (q.1.1 = j ∧ q.1.2 = i)
          then (squareSign M (circleShift M (x j)) -
            squareSign M (x j)) ^ 2 * ‖w‖ ^ 2 else 0) = _
        simp only [Finset.sum_ite]
        rw [hfilter]
        simp [target]
      rw [Finset.sum_congr rfl (fun x _ => hinner x)]
      rw [← Finset.sum_mul, sum_finBox_squareSign_circleShift_diff_sq]
    · have hji : j < i := by
        have hle : j ≤ i := le_of_not_gt hlt
        exact lt_of_le_of_ne hle (Ne.symm hij)
      let target : OrderedDirPair d := ⟨(j, i), hji⟩
      have hfilter :
          Finset.univ.filter (fun q : OrderedDirPair d =>
            (q.1.1 = i ∧ q.1.2 = j) ∨
              (q.1.1 = j ∧ q.1.2 = i)) = {target} := by
        ext q
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton]
        constructor
        · rintro (h | h)
          · have hq := q.2
            rcases h with ⟨h1, h2⟩
            rw [h1, h2] at hq
            omega
          · apply Subtype.ext
            rcases h with ⟨h1, h2⟩
            apply Prod.ext <;> assumption
        · rintro rfl
          exact Or.inr ⟨rfl, rfl⟩
      have hinner : ∀ x : FinBox d (M * 2),
          (∑ q : OrderedDirPair d,
            ‖covariantD1CLM ρ
                (trivialPhysicalGaugeBackground d (M * 2) Nc)
                (squareModeCochain d M Nc i j w)
                ((concretePlaquetteEquiv d (M * 2)).symm (x, q))‖ ^ 2)
            = (squareSign M (circleShift M (x j)) -
                squareSign M (x j)) ^ 2 * ‖w‖ ^ 2 := by
        intro x
        rw [Finset.sum_congr rfl (fun q _ =>
          norm_sq_covariantD1_squareMode_apply d M Nc ρ i j w
            ((concretePlaquetteEquiv d (M * 2)).symm (x, q)))]
        change (∑ q : OrderedDirPair d,
          if (q.1.1 = i ∧ q.1.2 = j) ∨ (q.1.1 = j ∧ q.1.2 = i)
          then (squareSign M (circleShift M (x j)) -
            squareSign M (x j)) ^ 2 * ‖w‖ ^ 2 else 0) = _
        simp only [Finset.sum_ite]
        rw [hfilter]
        simp [target]
      rw [Finset.sum_congr rfl (fun x _ => hinner x)]
      rw [← Finset.sum_mul, sum_finBox_squareSign_circleShift_diff_sq]

/-- **W-3b (exact Hodge energy of the square-wave mode).**

The square mode has precisely two jump walls.  If its bond direction and
modulation direction coincide, the entire energy is divergence energy; if
they differ, it is curl energy.  In either case the exact total is the same:
`8 · (2M)^(d-1) · ‖w‖²`.
-/
theorem flatGaugeHodgeK0_squareMode_energy
    (d M Nc : ℕ) [NeZero d] [NeZero M] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (i j : Fin d) (w : SUNLieCoord Nc) :
    inner ℝ (squareModeCochain d M Nc i j w)
        (flatGaugeHodgeK0CLM d (M * 2) Nc ρ
          (squareModeCochain d M Nc i j w))
      = 8 * ((M * 2 : ℕ) : ℝ) ^ (d - 1) * ‖w‖ ^ 2 := by
  rw [flatGaugeHodgeK0_inner_right,
    norm_sq_covariantD1_squareMode,
    norm_sq_gaugeConstraint_squareMode]
  by_cases hij : i = j <;> simp [hij]

/-- Division-free exact Rayleigh scaling for the W-3 mode:
`(2M) · ⟪A, K₀A⟫ = 8 · ‖A‖²`.  For a nonzero mode this is exactly the
Hodge quotient `8/(2M) = 4/M`, without introducing a denominator into the
formal statement. -/
theorem flatGaugeHodgeK0_squareMode_energy_mul_side
    (d M Nc : ℕ) [NeZero d] [NeZero M] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (i j : Fin d) (w : SUNLieCoord Nc) :
    ((M * 2 : ℕ) : ℝ) *
        inner ℝ (squareModeCochain d M Nc i j w)
          (flatGaugeHodgeK0CLM d (M * 2) Nc ρ
            (squareModeCochain d M Nc i j w))
      = 8 * ‖squareModeCochain d M Nc i j w‖ ^ 2 := by
  rw [flatGaugeHodgeK0_squareMode_energy,
    norm_sq_squareModeCochain]
  have hdpos : 0 < d := NeZero.pos d
  have hpow : ((M * 2 : ℕ) : ℝ) ^ d =
      ((M * 2 : ℕ) : ℝ) ^ (d - 1) * ((M * 2 : ℕ) : ℝ) := by
    calc
      ((M * 2 : ℕ) : ℝ) ^ d =
          ((M * 2 : ℕ) : ℝ) ^ ((d - 1) + 1) := by
            congr 1
            omega
      _ = ((M * 2 : ℕ) : ℝ) ^ (d - 1) *
          ((M * 2 : ℕ) : ℝ) := pow_succ _ _
  rw [hpow]
  ring

end YangMills.RG
