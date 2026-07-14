/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalPoincareLowModeFalsifier

/-!
# W-3b — exact flat-Hodge energy of the two-interface witness

This is the second brick of the ONE-SIDED W-3 falsifier.  W-3a constructed
the half-period square-wave cochain `squareModeCochain d M Nc i j w` on the
even torus of side `N = M + M`, proved exact orthogonality to constants, and
computed its exact norm.  This module evaluates only its flat Hodge term.

The hypotheses remain explicit: `d > 0`, `M > 0`, and `Nc > 0`; the side is
even by construction.  No lower bound `Nc ≥ 2` and no nonzero assumption on
`w` are needed for the identities.  At the trivial background the result is
independent of the chosen `SUNAdjointModel`, because only `Ad(1)` occurs.

The mechanism is separated exactly:

* if the bond and oscillation directions agree (`i = j`), the curl is zero
  and the backward divergence has two jump slices;
* if they differ (`i ≠ j`), the divergence is zero and the same two-slice
  energy is carried by the unique ordered plaquette plane `{i,j}`.

In both cases the exact endpoint is

`⟪A, K₀ A⟫ = 8 * (M + M)^(d - 1) * ‖w‖²`.

This is W-3b only: no block term, Rayleigh quotient, quotient-gate endpoint,
uniform CT claim, interacting Hessian, covariance root, `hRpoly`, mass gap,
or continuum statement is proved here.  A later W-3c may use this identity
inside the registered one-sided test; a bounded quotient on this family would
still not prove the quotient gate.

Oracle target: `[propext, Classical.choice, Quot.sound]`.  No sorry, no axioms.
-/

namespace YangMills.RG

open Matrix Module

def squareCycleSucc (M : ℕ) [NeZero M] (m : Fin (M + M)) : Fin (M + M) :=
  ⟨(m.val + 1) % (M + M), Nat.mod_lt _ (NeZero.pos (M + M))⟩

def squareLeftInterface (M : ℕ) [NeZero M] : Fin (M + M) :=
  ⟨M - 1, by have := NeZero.ne M; omega⟩

def squareRightInterface (M : ℕ) [NeZero M] : Fin (M + M) :=
  ⟨M + M - 1, by have := NeZero.ne M; omega⟩

theorem squareLeftInterface_ne_rightInterface (M : ℕ) [NeZero M] :
    squareLeftInterface M ≠ squareRightInterface M := by
  intro h
  have hv := congrArg Fin.val h
  simp only [squareLeftInterface, squareRightInterface] at hv
  have := NeZero.ne M
  omega

theorem squareSign_cycleSucc_diff_sq (M : ℕ) [NeZero M]
    (m : Fin (M + M)) :
    (squareSign M m - squareSign M (squareCycleSucc M m)) ^ 2 =
      (if m = squareLeftInterface M then 4 else 0) +
        (if m = squareRightInterface M then 4 else 0) := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hm : m.val < M + M := m.isLt
  by_cases hfirst : m.val < M
  · by_cases hlast : m.val + 1 = M
    · have hmleft : m = squareLeftInterface M := by
        apply Fin.ext
        simp only [squareLeftInterface]
        omega
      have hmright : m ≠ squareRightInterface M := by
        rw [hmleft]
        exact squareLeftInterface_ne_rightInterface M
      rw [if_pos hmleft, if_neg hmright]
      unfold squareSign squareCycleSucc
      simp only [hfirst, if_true]
      have hsuccmod : (m.val + 1) % (M + M) = M := by
        rw [hlast, Nat.mod_eq_of_lt]
        omega
      simp only [hsuccmod, lt_self_iff_false, if_false]
      norm_num
    · have hsuccfirst : m.val + 1 < M := by omega
      have hmleft : m ≠ squareLeftInterface M := by
        intro h
        have hv := congrArg Fin.val h
        simp only [squareLeftInterface] at hv
        omega
      have hmright : m ≠ squareRightInterface M := by
        intro h
        have hv := congrArg Fin.val h
        simp only [squareRightInterface] at hv
        omega
      rw [if_neg hmleft, if_neg hmright]
      unfold squareSign squareCycleSucc
      simp only [hfirst, if_true]
      have hsuccmod : (m.val + 1) % (M + M) = m.val + 1 :=
        Nat.mod_eq_of_lt (by omega)
      simp only [hsuccmod, hsuccfirst, if_true]
      norm_num
  · by_cases hlast : m.val + 1 = M + M
    · have hmright : m = squareRightInterface M := by
        apply Fin.ext
        simp only [squareRightInterface]
        omega
      have hmleft : m ≠ squareLeftInterface M := by
        intro h
        apply squareLeftInterface_ne_rightInterface M
        exact h.symm.trans hmright
      rw [if_neg hmleft, if_pos hmright]
      unfold squareSign squareCycleSucc
      simp only [hfirst, if_false]
      have hsuccmod : (m.val + 1) % (M + M) = 0 := by
        rw [hlast, Nat.mod_self]
      simp only [hsuccmod, hM, if_true]
      norm_num
    · have hsucc : m.val + 1 < M + M := by omega
      have hmleft : m ≠ squareLeftInterface M := by
        intro h
        have hv := congrArg Fin.val h
        simp only [squareLeftInterface] at hv
        omega
      have hmright : m ≠ squareRightInterface M := by
        intro h
        have hv := congrArg Fin.val h
        simp only [squareRightInterface] at hv
        omega
      rw [if_neg hmleft, if_neg hmright]
      unfold squareSign squareCycleSucc
      simp only [hfirst, if_false]
      have hsuccmod : (m.val + 1) % (M + M) = m.val + 1 :=
        Nat.mod_eq_of_lt hsucc
      have hsuccsecond : ¬m.val + 1 < M := by omega
      simp only [hsuccmod, hsuccsecond, if_false]
      norm_num

theorem sum_squareSign_cycleSucc_diff_sq (M : ℕ) [NeZero M] :
    (∑ m : Fin (M + M),
      (squareSign M m - squareSign M (squareCycleSucc M m)) ^ 2) = 8 := by
  rw [Finset.sum_congr rfl (fun m _ => squareSign_cycleSucc_diff_sq M m)]
  rw [Finset.sum_add_distrib]
  simp
  norm_num

theorem squareCycleSucc_eq_shift_coord {d M : ℕ} [NeZero M]
    (x : FinBox d (M + M)) (j : Fin d) :
    squareCycleSucc M (x j) = (x.shift j) j := by
  apply Fin.ext
  simp [squareCycleSucc, FinBox.shift]

theorem card_other_coordinates (d : ℕ) (j : Fin d) :
    Fintype.card {k : Fin d // k ≠ j} = d - 1 := by
  rw [Fintype.card_subtype_compl (fun k : Fin d => k = j)]
  simp

theorem sum_finBox_squareSign_cycleSucc_diff_sq (d M : ℕ) [NeZero M]
    (j : Fin d) :
    (∑ x : FinBox d (M + M),
      (squareSign M (x j) - squareSign M (squareCycleSucc M (x j))) ^ 2) =
        8 * ((M + M : ℕ) : ℝ) ^ (d - 1) := by
  classical
  have hsplit :
      (∑ x : FinBox d (M + M),
        (squareSign M (x j) - squareSign M (squareCycleSucc M (x j))) ^ 2) =
      ∑ p : Fin (M + M) × ({k : Fin d // k ≠ j} → Fin (M + M)),
        (squareSign M p.1 - squareSign M (squareCycleSucc M p.1)) ^ 2 := by
    rw [← Equiv.sum_comp (Equiv.piSplitAt j (fun _ : Fin d => Fin (M + M)))
      (fun p => (squareSign M p.1 - squareSign M (squareCycleSucc M p.1)) ^ 2)]
    rfl
  rw [hsplit, Fintype.sum_prod_type]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.mul_sum, sum_squareSign_cycleSucc_diff_sq]
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    card_other_coordinates d j]
  push_cast
  ring

theorem sum_finBox_squareSign_shift_diff_sq (d M : ℕ) [NeZero M]
    (j : Fin d) :
    (∑ x : FinBox d (M + M),
      (squareSign M (x j) - squareSign M ((x.shift j) j)) ^ 2) =
        8 * ((M + M : ℕ) : ℝ) ^ (d - 1) := by
  simpa only [← squareCycleSucc_eq_shift_coord] using
    sum_finBox_squareSign_cycleSucc_diff_sq d M j

theorem sum_finBox_squareSign_shiftBack_diff_sq (d M : ℕ) [NeZero M]
    (j : Fin d) :
    (∑ x : FinBox d (M + M),
      (squareSign M (x j) - squareSign M ((x.shiftBack j) j)) ^ 2) =
        8 * ((M + M : ℕ) : ℝ) ^ (d - 1) := by
  let f : FinBox d (M + M) → ℝ := fun x =>
    (squareSign M (x j) - squareSign M ((x.shiftBack j) j)) ^ 2
  have hshift := FinBox.sum_shift f j
  have hterm : ∀ x : FinBox d (M + M),
      f (x.shift j) =
        (squareSign M (x j) - squareSign M ((x.shift j) j)) ^ 2 := by
    intro x
    simp only [f, FinBox.shiftBack_shift]
    ring
  rw [Finset.sum_congr rfl (fun x _ => hterm x)] at hshift
  rw [← hshift]
  exact sum_finBox_squareSign_shift_diff_sq d M j

theorem covariantD1CLM_squareModeCochain_diagonal_eq_zero
    (d M Nc : ℕ) [NeZero d] [NeZero M] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (i : Fin d) (w : SUNLieCoord Nc) :
    covariantD1CLM ρ (trivialPhysicalGaugeBackground d (M + M) Nc)
        (squareModeCochain d M Nc i i w) = 0 := by
  apply PiLp.ext
  intro p
  change covariantD1CLM ρ (trivialPhysicalGaugeBackground d (M + M) Nc)
      (squareModeCochain d M Nc i i w) p = 0
  rw [covariantD1CLM_trivial_apply]
  cases p with
  | mk site dir1 dir2 hlt =>
      simp only [squareModeCochain_apply]
      by_cases h1 : dir1 = i <;> by_cases h2 : dir2 = i
      · subst dir1
        subst dir2
        simp at hlt
      · simp only [h1, h2, if_true, if_false]
        have hcoord : (FinBox.shift site dir2) i = site i := by
          simp [FinBox.shift, Ne.symm h2]
        rw [hcoord]
        abel
      · simp only [h1, h2, if_true, if_false]
        have hcoord : (FinBox.shift site dir1) i = site i := by
          simp [FinBox.shift, Ne.symm h1]
        rw [hcoord]
        abel
      · simp [h1, h2]

theorem covariantD1CLM_squareModeCochain_apply
    (d M Nc : ℕ) [NeZero d] [NeZero M] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (i j : Fin d) (w : SUNLieCoord Nc)
    (p : ConcretePlaquette d (M + M)) :
    covariantD1CLM ρ (trivialPhysicalGaugeBackground d (M + M) Nc)
        (squareModeCochain d M Nc i j w) p =
      if p.dir1 = i then
        (squareSign M (p.site j) -
          squareSign M ((p.site.shift p.dir2) j)) • w
      else if p.dir2 = i then
        (squareSign M ((p.site.shift p.dir1) j) -
          squareSign M (p.site j)) • w
      else 0 := by
  rw [covariantD1CLM_trivial_apply]
  simp only [squareModeCochain_apply]
  by_cases h1 : p.dir1 = i <;> by_cases h2 : p.dir2 = i
  · exfalso
    have := p.hlt
    omega
  · simp [h1, h2, sub_smul]
  · simp [h1, h2, sub_smul]
  · simp [h1, h2]

abbrev OrderedDirectionPair (d : ℕ) :=
  {q : Fin d × Fin d // q.1 < q.2}

def concretePlaquetteEquivOrderedPair (d N : ℕ) :
    ConcretePlaquette d N ≃ FinBox d N × OrderedDirectionPair d where
  toFun p := (p.site, ⟨(p.dir1, p.dir2), p.hlt⟩)
  invFun z := ⟨z.1, z.2.1.1, z.2.1.2, z.2.2⟩
  left_inv p := by cases p; rfl
  right_inv z := by rcases z with ⟨x, ⟨⟨a, b⟩, hab⟩⟩; rfl

theorem gaugeConstraintQCLM_squareModeCochain_apply
    (d M Nc : ℕ) [NeZero d] [NeZero M] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (i j : Fin d) (w : SUNLieCoord Nc)
    (x : FinBox d (M + M)) :
    gaugeConstraintQCLM ρ (trivialPhysicalGaugeBackground d (M + M) Nc)
        (squareModeCochain d M Nc i j w) x =
      (squareSign M (x j) - squareSign M ((x.shiftBack i) j)) • w := by
  rw [gaugeConstraintQCLM_trivial_apply]
  have hterm : ∀ k : Fin d,
      (squareModeCochain d M Nc i j w (x, k) -
        squareModeCochain d M Nc i j w (x.shiftBack k, k)) =
      if k = i then
        squareSign M (x j) • w - squareSign M ((x.shiftBack i) j) • w
      else 0 := by
    intro k
    rw [squareModeCochain_apply, squareModeCochain_apply]
    by_cases hk : k = i
    · subst k
      simp
    · simp [hk]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  rw [Finset.sum_ite_eq' Finset.univ i]
  simp only [Finset.mem_univ, if_true]
  rw [sub_smul]

theorem gaugeConstraintQCLM_squareModeCochain_eq_zero_of_ne
    (d M Nc : ℕ) [NeZero d] [NeZero M] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (i j : Fin d) (hij : i ≠ j)
    (w : SUNLieCoord Nc) :
    gaugeConstraintQCLM ρ (trivialPhysicalGaugeBackground d (M + M) Nc)
        (squareModeCochain d M Nc i j w) = 0 := by
  apply PiLp.ext
  intro x
  change gaugeConstraintQCLM ρ
      (trivialPhysicalGaugeBackground d (M + M) Nc)
      (squareModeCochain d M Nc i j w) x = 0
  rw [gaugeConstraintQCLM_squareModeCochain_apply]
  have hcoord : (x.shiftBack i) j = x j := by
    simp [FinBox.shiftBack, Ne.symm hij]
  rw [hcoord, sub_self, zero_smul]

theorem norm_sq_covariantD1CLM_squareModeCochain_of_ne
    (d M Nc : ℕ) [NeZero d] [NeZero M] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (i j : Fin d) (hij : i ≠ j)
    (w : SUNLieCoord Nc) :
    ‖covariantD1CLM ρ (trivialPhysicalGaugeBackground d (M + M) Nc)
        (squareModeCochain d M Nc i j w)‖ ^ 2 =
      8 * ((M + M : ℕ) : ℝ) ^ (d - 1) * ‖w‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  let D := covariantD1CLM ρ
    (trivialPhysicalGaugeBackground d (M + M) Nc)
      (squareModeCochain d M Nc i j w)
  let e := concretePlaquetteEquivOrderedPair d (M + M)
  have hsplit :
      (∑ p : ConcretePlaquette d (M + M), ‖D p‖ ^ 2) =
        ∑ z : FinBox d (M + M) × OrderedDirectionPair d,
          ‖D (e.symm z)‖ ^ 2 := by
    have h := e.sum_comp (fun z => ‖D (e.symm z)‖ ^ 2)
    simpa using h
  rw [hsplit, Fintype.sum_prod_type]
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · let q0 : OrderedDirectionPair d := ⟨(i, j), hijlt⟩
    have hpoint : ∀ (x : FinBox d (M + M)) (q : OrderedDirectionPair d),
        ‖D (e.symm (x, q))‖ ^ 2 =
          if q = q0 then
            (squareSign M (x j) - squareSign M ((x.shift j) j)) ^ 2 * ‖w‖ ^ 2
          else 0 := by
      intro x q
      change
        ‖covariantD1CLM ρ (trivialPhysicalGaugeBackground d (M + M) Nc)
          (squareModeCochain d M Nc i j w)
          ⟨x, q.1.1, q.1.2, q.2⟩‖ ^ 2 = _
      by_cases hq : q = q0
      · subst q
        rw [if_pos rfl, covariantD1CLM_squareModeCochain_apply]
        simp only [q0, if_pos, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      · rw [if_neg hq, covariantD1CLM_squareModeCochain_apply]
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
          rw [hcoord, sub_self, zero_smul, norm_zero]
          norm_num
        · by_cases h2 : q.1.2 = i
          · have hnotj : q.1.1 ≠ j := by
              intro hdir
              have := q.2
              omega
            simp only [h1, h2, if_false, if_true]
            have hcoord : (x.shift q.1.1) j = x j := by
              simp [FinBox.shift, Ne.symm hnotj]
            rw [hcoord, sub_self, zero_smul, norm_zero]
            norm_num
          · simp [h1, h2]
    rw [Finset.sum_congr rfl (fun x _ =>
      Finset.sum_congr rfl (fun q _ => hpoint x q))]
    simp only [Finset.sum_ite_eq' Finset.univ q0, Finset.mem_univ, if_true]
    rw [← Finset.sum_mul, sum_finBox_squareSign_shift_diff_sq]
  · let q0 : OrderedDirectionPair d := ⟨(j, i), hjilt⟩
    have hpoint : ∀ (x : FinBox d (M + M)) (q : OrderedDirectionPair d),
        ‖D (e.symm (x, q))‖ ^ 2 =
          if q = q0 then
            (squareSign M (x j) - squareSign M ((x.shift j) j)) ^ 2 * ‖w‖ ^ 2
          else 0 := by
      intro x q
      change
        ‖covariantD1CLM ρ (trivialPhysicalGaugeBackground d (M + M) Nc)
          (squareModeCochain d M Nc i j w)
          ⟨x, q.1.1, q.1.2, q.2⟩‖ ^ 2 = _
      by_cases hq : q = q0
      · subst q
        rw [if_pos rfl, covariantD1CLM_squareModeCochain_apply]
        simp only [q0, if_neg (Ne.symm hij), if_pos, norm_smul, mul_pow,
          Real.norm_eq_abs, sq_abs]
        ring
      · rw [if_neg hq, covariantD1CLM_squareModeCochain_apply]
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
          rw [hcoord, sub_self, zero_smul, norm_zero]
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
            rw [hcoord, sub_self, zero_smul, norm_zero]
            norm_num
          · simp [h1, h2]
    rw [Finset.sum_congr rfl (fun x _ =>
      Finset.sum_congr rfl (fun q _ => hpoint x q))]
    simp only [Finset.sum_ite_eq' Finset.univ q0, Finset.mem_univ, if_true]
    rw [← Finset.sum_mul, sum_finBox_squareSign_shift_diff_sq]

theorem gaugeConstraintQCLM_squareModeCochain_diagonal_apply
    (d M Nc : ℕ) [NeZero d] [NeZero M] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (i : Fin d) (w : SUNLieCoord Nc)
    (x : FinBox d (M + M)) :
    gaugeConstraintQCLM ρ (trivialPhysicalGaugeBackground d (M + M) Nc)
        (squareModeCochain d M Nc i i w) x =
      (squareSign M (x i) - squareSign M ((x.shiftBack i) i)) • w := by
  exact gaugeConstraintQCLM_squareModeCochain_apply d M Nc ρ i i w x

theorem norm_sq_gaugeConstraintQCLM_squareModeCochain_diagonal
    (d M Nc : ℕ) [NeZero d] [NeZero M] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (i : Fin d) (w : SUNLieCoord Nc) :
    ‖gaugeConstraintQCLM ρ (trivialPhysicalGaugeBackground d (M + M) Nc)
        (squareModeCochain d M Nc i i w)‖ ^ 2 =
      8 * ((M + M : ℕ) : ℝ) ^ (d - 1) * ‖w‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  have hterm : ∀ x : FinBox d (M + M),
      ‖gaugeConstraintQCLM ρ (trivialPhysicalGaugeBackground d (M + M) Nc)
          (squareModeCochain d M Nc i i w) x‖ ^ 2 =
        (squareSign M (x i) - squareSign M ((x.shiftBack i) i)) ^ 2 * ‖w‖ ^ 2 := by
    intro x
    rw [gaugeConstraintQCLM_squareModeCochain_diagonal_apply]
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [Finset.sum_congr rfl (fun x _ => hterm x)]
  rw [← Finset.sum_mul, sum_finBox_squareSign_shiftBack_diff_sq]

theorem norm_sq_covariantD1CLM_squareModeCochain
    (d M Nc : ℕ) [NeZero d] [NeZero M] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (i j : Fin d) (w : SUNLieCoord Nc) :
    ‖covariantD1CLM ρ (trivialPhysicalGaugeBackground d (M + M) Nc)
        (squareModeCochain d M Nc i j w)‖ ^ 2 =
      if i = j then 0
      else 8 * ((M + M : ℕ) : ℝ) ^ (d - 1) * ‖w‖ ^ 2 := by
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, covariantD1CLM_squareModeCochain_diagonal_eq_zero,
      norm_zero]
    norm_num
  · rw [if_neg hij]
    exact norm_sq_covariantD1CLM_squareModeCochain_of_ne d M Nc ρ i j hij w

theorem norm_sq_gaugeConstraintQCLM_squareModeCochain
    (d M Nc : ℕ) [NeZero d] [NeZero M] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (i j : Fin d) (w : SUNLieCoord Nc) :
    ‖gaugeConstraintQCLM ρ (trivialPhysicalGaugeBackground d (M + M) Nc)
        (squareModeCochain d M Nc i j w)‖ ^ 2 =
      if i = j then 8 * ((M + M : ℕ) : ℝ) ^ (d - 1) * ‖w‖ ^ 2
      else 0 := by
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    exact norm_sq_gaugeConstraintQCLM_squareModeCochain_diagonal d M Nc ρ i w
  · rw [if_neg hij, gaugeConstraintQCLM_squareModeCochain_eq_zero_of_ne
      d M Nc ρ i j hij w, norm_zero]
    norm_num

theorem flatGaugeHodgeK0_inner_squareModeCochain_diagonal
    (d M Nc : ℕ) [NeZero d] [NeZero M] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (i : Fin d) (w : SUNLieCoord Nc) :
    inner ℝ (squareModeCochain d M Nc i i w)
        (flatGaugeHodgeK0CLM d (M + M) Nc ρ
          (squareModeCochain d M Nc i i w)) =
      8 * ((M + M : ℕ) : ℝ) ^ (d - 1) * ‖w‖ ^ 2 := by
  rw [flatGaugeHodgeK0_inner_right]
  rw [covariantD1CLM_squareModeCochain_diagonal_eq_zero, norm_zero]
  rw [norm_sq_gaugeConstraintQCLM_squareModeCochain_diagonal]
  norm_num

theorem flatGaugeHodgeK0_inner_squareModeCochain
    (d M Nc : ℕ) [NeZero d] [NeZero M] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (i j : Fin d) (w : SUNLieCoord Nc) :
    inner ℝ (squareModeCochain d M Nc i j w)
        (flatGaugeHodgeK0CLM d (M + M) Nc ρ
          (squareModeCochain d M Nc i j w)) =
      8 * ((M + M : ℕ) : ℝ) ^ (d - 1) * ‖w‖ ^ 2 := by
  rw [flatGaugeHodgeK0_inner_right]
  rw [norm_sq_covariantD1CLM_squareModeCochain,
    norm_sq_gaugeConstraintQCLM_squareModeCochain]
  by_cases hij : i = j <;> simp [hij]

end YangMills.RG
