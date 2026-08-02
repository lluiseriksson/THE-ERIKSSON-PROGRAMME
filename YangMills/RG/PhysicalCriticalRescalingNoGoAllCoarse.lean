/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalCriticalRescalingNoGo

/-!
# Block-periodic critical-rescaling no-go at every coarse side

This module repeats the even square profile inside every `L = 2M` block.
The resulting transverse mode has zero block average at every coarse bond,
independently of the positive coarse side `N'`.  Its norm and Hodge energy
retain the same Rayleigh quotient `8/L` as the one-coarse-site witness.
-/

namespace YangMills.RG

open Matrix Module

/-! ## Block/offset coordinates -/

/-- Fine site with coarse block coordinate `y` and within-block offset `r`. -/
def blockOffsetSite {d : ℕ} (L N' : ℕ) [NeZero L]
    (y : FinBox d N') (r : Fin d → Fin L) : FinBox d (L * N') :=
  fun i => ⟨L * (y i).val + (r i).val, by
    have hr := (r i).isLt
    have hy := (y i).isLt
    have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
    nlinarith⟩

@[simp]
theorem blockOffsetSite_val {d L N' : ℕ} [NeZero L]
    (y : FinBox d N') (r : Fin d → Fin L) (i : Fin d) :
    (blockOffsetSite L N' y r i).val = L * (y i).val + (r i).val := rfl

theorem blockOffsetSite_injective {d L N' : ℕ} [NeZero L]
    (y : FinBox d N') : Function.Injective (blockOffsetSite L N' y) := by
  intro r s h
  funext i
  have hi := congrArg Fin.val (congrFun h i)
  exact Fin.ext (by simpa only [blockOffsetSite_val] using Nat.add_left_cancel hi)

theorem blockOffsetSite_mem_blockOf {d L N' : ℕ} [NeZero L]
    (y : FinBox d N') (r : Fin d → Fin L) :
    blockOffsetSite L N' y r ∈ blockOf L N' y := by
  rw [mem_blockOf, blockSite_eq_iff_cube]
  intro i
  simp only [blockOffsetSite_val]
  constructor <;> omega

theorem blockOf_eq_image_blockOffsetSite {d L N' : ℕ} [NeZero L]
    (y : FinBox d N') :
    blockOf L N' y = Finset.univ.image (blockOffsetSite L N' y) := by
  apply Finset.Subset.antisymm
  · intro x hx
    rw [mem_blockOf, blockSite_eq_iff_cube] at hx
    let r : Fin d → Fin L := fun i =>
      ⟨(x i).val - L * (y i).val, by
        have h1 := (hx i).1
        have h2 := (hx i).2
        omega⟩
    apply Finset.mem_image.mpr
    refine ⟨r, Finset.mem_univ _, ?_⟩
    funext i
    apply Fin.ext
    simp only [blockOffsetSite_val, r]
    have h1 := (hx i).1
    omega
  · intro x hx
    obtain ⟨r, _hr, rfl⟩ := Finset.mem_image.mp hx
    exact blockOffsetSite_mem_blockOf y r

theorem sum_blockOf_eq_sum_offsets {d L N' : ℕ} [NeZero L]
    {V : Type*} [AddCommMonoid V] (y : FinBox d N')
    (F : FinBox d (L * N') → V) :
    ∑ x ∈ blockOf L N' y, F x =
      ∑ r : Fin d → Fin L, F (blockOffsetSite L N' y r) := by
  rw [blockOf_eq_image_blockOffsetSite]
  rw [Finset.sum_image]
  intro r _ s _ hrs
  exact blockOffsetSite_injective y hrs

/-! ## The square profile repeated inside every block -/

/-- Offset of a fine coordinate inside its `2M` block. -/
def periodicSquareOffset (M N' : ℕ) [NeZero M]
    (m : Fin ((M + M) * N')) : Fin (M + M) :=
  ⟨m.val % (M + M), Nat.mod_lt _ (by
    have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
    omega)⟩

/-- The `+1`/`-1` square profile repeated in every block. -/
def blockPeriodicSquareSign (M N' : ℕ) [NeZero M]
    (m : Fin ((M + M) * N')) : ℝ :=
  squareSign M (periodicSquareOffset M N' m)

@[simp]
theorem blockPeriodicSquareSign_sq (M N' : ℕ) [NeZero M]
    (m : Fin ((M + M) * N')) :
    blockPeriodicSquareSign M N' m ^ 2 = 1 := by
  exact squareSign_sq M (periodicSquareOffset M N' m)

@[simp]
theorem periodicSquareOffset_blockOffsetSite
    {d M N' : ℕ} [NeZero M] (y : FinBox d N')
    (r : Fin d → Fin (M + M)) (j : Fin d) :
    periodicSquareOffset M N'
        (blockOffsetSite (M + M) N' y r j) = r j := by
  apply Fin.ext
  simp only [periodicSquareOffset, blockOffsetSite_val]
  rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (r j).isLt]

theorem sum_blockPeriodicSquareSign_block_eq_zero
    {d M N' : ℕ} [NeZero M] (y : FinBox d N') (j : Fin d) :
    ∑ x ∈ blockOf (d := d) (M + M) N' y,
      blockPeriodicSquareSign M N' (x j) = 0 := by
  rw [sum_blockOf_eq_sum_offsets]
  simp only [blockPeriodicSquareSign, periodicSquareOffset_blockOffsetSite]
  have hsplit :
      (∑ r : Fin d → Fin (M + M), squareSign M (r j)) =
        ∑ p : Fin (M + M) × ({k : Fin d // k ≠ j} → Fin (M + M)),
          squareSign M p.1 := by
    rw [← Equiv.sum_comp
      (Equiv.piSplitAt j (fun _ : Fin d => Fin (M + M)))
      (fun p => squareSign M p.1)]
    rfl
  rw [hsplit, Fintype.sum_prod_type]
  simp only [Finset.sum_const]
  rw [← Finset.smul_sum, sum_squareSign, smul_zero]

theorem blockPeriodicSquareSign_iterate_shift_other
    {d M N' : ℕ} [NeZero M] [NeZero N']
    (x : FinBox d ((M + M) * N')) (i j : Fin d) (hij : i ≠ j) (k : ℕ) :
    blockPeriodicSquareSign M N'
        (((fun z => FinBox.shift z i)^[k] x) j) =
      blockPeriodicSquareSign M N' (x j) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      have hcoord : (FinBox.shift ((fun z => FinBox.shift z i)^[k] x) i) j =
          ((fun z => FinBox.shift z i)^[k] x) j := by
        simp [FinBox.shift, Ne.symm hij]
      rw [hcoord, ih]

/-- Quotient/remainder coordinates for a one-dimensional fine cycle. -/
def periodicCoordinateEquiv (M N' : ℕ) :
    Fin N' × Fin (M + M) ≃ Fin ((M + M) * N') :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm N' (M + M)))

@[simp]
theorem periodicSquareOffset_periodicCoordinateEquiv
    (M N' : ℕ) [NeZero M] (p : Fin N' × Fin (M + M)) :
    periodicSquareOffset M N' (periodicCoordinateEquiv M N' p) = p.2 := by
  apply Fin.ext
  simp [periodicSquareOffset, periodicCoordinateEquiv,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt p.2.isLt]

/-- Successor on the full fine coordinate cycle. -/
def periodicCycleSucc (M N' : ℕ) [NeZero M] [NeZero N']
    (m : Fin ((M + M) * N')) : Fin ((M + M) * N') :=
  ⟨(m.val + 1) % ((M + M) * N'), Nat.mod_lt _ (by
    have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
    have hN' : 0 < N' := Nat.pos_of_ne_zero (NeZero.ne N')
    exact Nat.mul_pos (by omega) hN')⟩

theorem periodicSquareOffset_periodicCycleSucc
    (M N' : ℕ) [NeZero M] [NeZero N']
    (m : Fin ((M + M) * N')) :
    periodicSquareOffset M N' (periodicCycleSucc M N' m) =
      squareCycleSucc M (periodicSquareOffset M N' m) := by
  apply Fin.ext
  simp only [periodicSquareOffset, periodicCycleSucc, squareCycleSucc]
  have hdvd : M + M ∣ (M + M) * N' := dvd_mul_right _ _
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hone : 1 % (M + M) = 1 := Nat.mod_eq_of_lt (by omega)
  rw [Nat.mod_mod_of_dvd _ hdvd, Nat.add_mod, hone]

theorem sum_blockPeriodicSquareSign_cycleSucc_diff_sq
    (M N' : ℕ) [NeZero M] [NeZero N'] :
    (∑ m : Fin ((M + M) * N'),
      (blockPeriodicSquareSign M N' m -
        blockPeriodicSquareSign M N' (periodicCycleSucc M N' m)) ^ 2) =
      8 * (N' : ℝ) := by
  have he := (periodicCoordinateEquiv M N').sum_comp
    (fun m : Fin ((M + M) * N') =>
    (blockPeriodicSquareSign M N' m -
      blockPeriodicSquareSign M N' (periodicCycleSucc M N' m)) ^ 2)
  calc
    (∑ m : Fin ((M + M) * N'),
      (blockPeriodicSquareSign M N' m -
        blockPeriodicSquareSign M N' (periodicCycleSucc M N' m)) ^ 2) =
        ∑ p : Fin N' × Fin (M + M),
          (squareSign M p.2 - squareSign M (squareCycleSucc M p.2)) ^ 2 := by
            rw [← he]
            apply Finset.sum_congr rfl
            intro p hp
            simp only [blockPeriodicSquareSign,
              periodicSquareOffset_periodicCoordinateEquiv,
              periodicSquareOffset_periodicCycleSucc]
    _ = 8 * (N' : ℝ) := by
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_congr rfl (fun _ _ =>
        sum_squareSign_cycleSucc_diff_sq M)]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring

theorem periodicCycleSucc_eq_shift_coord
    {d M N' : ℕ} [NeZero M] [NeZero N']
    (x : FinBox d ((M + M) * N')) (j : Fin d) :
    periodicCycleSucc M N' (x j) = (x.shift j) j := by
  apply Fin.ext
  simp [periodicCycleSucc, FinBox.shift]

theorem sum_finBox_blockPeriodicSquareSign_shift_diff_sq
    (d M N' : ℕ) [NeZero M] [NeZero N'] (j : Fin d) :
    (∑ x : FinBox d ((M + M) * N'),
      (blockPeriodicSquareSign M N' (x j) -
        blockPeriodicSquareSign M N' ((x.shift j) j)) ^ 2) =
      8 * (N' : ℝ) * ((((M + M) * N' : ℕ) : ℝ) ^ (d - 1)) := by
  classical
  have hsplit :
      (∑ x : FinBox d ((M + M) * N'),
        (blockPeriodicSquareSign M N' (x j) -
          blockPeriodicSquareSign M N' (periodicCycleSucc M N' (x j))) ^ 2) =
        ∑ p : Fin ((M + M) * N') ×
            ({k : Fin d // k ≠ j} → Fin ((M + M) * N')),
          (blockPeriodicSquareSign M N' p.1 -
            blockPeriodicSquareSign M N' (periodicCycleSucc M N' p.1)) ^ 2 := by
    rw [← Equiv.sum_comp
      (Equiv.piSplitAt j
        (fun _ : Fin d => Fin ((M + M) * N')))
      (fun p => (blockPeriodicSquareSign M N' p.1 -
        blockPeriodicSquareSign M N' (periodicCycleSucc M N' p.1)) ^ 2)]
    rfl
  have hcycle :
      (∑ x : FinBox d ((M + M) * N'),
        (blockPeriodicSquareSign M N' (x j) -
          blockPeriodicSquareSign M N' (periodicCycleSucc M N' (x j))) ^ 2) =
        8 * (N' : ℝ) * ((((M + M) * N' : ℕ) : ℝ) ^ (d - 1)) := by
    rw [hsplit, Fintype.sum_prod_type]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [← Finset.mul_sum, sum_blockPeriodicSquareSign_cycleSucc_diff_sq]
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      card_other_coordinates d j]
    push_cast
    ring
  simpa only [periodicCycleSucc_eq_shift_coord] using hcycle

/-! ## The block-periodic transverse cochain -/

noncomputable def blockPeriodicSquareModeCochain
    (d M N' Nc : ℕ) [NeZero M] [NeZero N']
    (i j : Fin d) (w : SUNLieCoord Nc) :
    FinePhysicalOneCochain d (M + M) N' Nc :=
  WithLp.toLp 2 fun b : PhysicalBond d ((M + M) * N') =>
    if b.2 = i then blockPeriodicSquareSign M N' (b.1 j) • w else 0

@[simp]
theorem blockPeriodicSquareModeCochain_apply
    {d M N' Nc : ℕ} [NeZero M] [NeZero N']
    (i j : Fin d) (w : SUNLieCoord Nc)
    (b : PhysicalBond d ((M + M) * N')) :
    blockPeriodicSquareModeCochain d M N' Nc i j w b =
      if b.2 = i then blockPeriodicSquareSign M N' (b.1 j) • w else 0 := rfl

theorem norm_sq_blockPeriodicSquareModeCochain
    (d M N' Nc : ℕ) [NeZero M] [NeZero N']
    (i j : Fin d) (w : SUNLieCoord Nc) :
    ‖blockPeriodicSquareModeCochain d M N' Nc i j w‖ ^ 2 =
      ((((M + M) * N' : ℕ) : ℝ) ^ d) * ‖w‖ ^ 2 := by
  classical
  rw [PiLp.norm_sq_eq_of_L2]
  have hterm : ∀ b : PhysicalBond d ((M + M) * N'),
      ‖blockPeriodicSquareModeCochain d M N' Nc i j w b‖ ^ 2 =
        if b.2 = i then ‖w‖ ^ 2 else 0 := by
    intro b
    rw [blockPeriodicSquareModeCochain_apply]
    by_cases hb : b.2 = i
    · rw [if_pos hb, if_pos hb, norm_smul, mul_pow, Real.norm_eq_abs,
        sq_abs, blockPeriodicSquareSign_sq, one_mul]
    · rw [if_neg hb, if_neg hb, norm_zero]
      norm_num
  rw [Finset.sum_congr rfl (fun b _ => hterm b)]
  rw [Fintype.sum_prod_type]
  have hinner : ∀ _x : FinBox d ((M + M) * N'),
      (∑ k : Fin d, if k = i then ‖w‖ ^ 2 else 0) = ‖w‖ ^ 2 :=
    fun _x => (Finset.sum_ite_eq' Finset.univ i (fun _ => ‖w‖ ^ 2)).trans
      (if_pos (Finset.mem_univ i))
  rw [Finset.sum_congr rfl (fun x _ => hinner x)]
  rw [Finset.sum_const, Finset.card_univ, card_finBox, nsmul_eq_mul]
  push_cast
  ring

theorem flatBlockConstraintQCLM_blockPeriodicSquareMode_eq_zero
    {d M N' Nc : ℕ} [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]
    (i j : Fin d) (hij : i ≠ j) (w : SUNLieCoord Nc) :
    flatBlockConstraintQCLM (d := d) (Nc := Nc) (M + M) N'
        (blockPeriodicSquareModeCochain d M N' Nc i j w) = 0 := by
  classical
  apply PiLp.ext
  intro b
  change flatBlockConstraintQCLM (d := d) (Nc := Nc) (M + M) N'
      (blockPeriodicSquareModeCochain d M N' Nc i j w) b = 0
  rw [flatBlockConstraintQCLM_apply]
  unfold linAvg fineLineSum
  by_cases hb : b.2 = i
  · subst i
    have hsum :
        (∑ x ∈ blockOf (M + M) N' b.1,
          ∑ k ∈ Finset.range (M + M),
            blockPeriodicSquareSign M N'
              (((fun z => FinBox.shift z b.2)^[k] x) j) • w) = 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.sum_congr rfl (fun x _ => by
        rw [blockPeriodicSquareSign_iterate_shift_other x b.2 j hij k])]
      rw [← Finset.sum_smul,
        sum_blockPeriodicSquareSign_block_eq_zero b.1 j, zero_smul]
    simp only [physicalBondOfEdge_mk_true,
      blockPeriodicSquareModeCochain_apply, if_true]
    rw [hsum, smul_zero]
  · simp only [physicalBondOfEdge_mk_true,
      blockPeriodicSquareModeCochain_apply, hb, if_false,
      Finset.sum_const_zero, smul_zero]

theorem criticalScaledBlockConstraintQCLM_blockPeriodicSquareMode_eq_zero
    {d M N' Nc : ℕ} [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]
    (i j : Fin d) (hij : i ≠ j) (w : SUNLieCoord Nc) :
    scaledFlatBlockConstraintQCLM (d := d) (Nc := Nc)
        (((M + M : ℕ) : ℝ))
        (blockPeriodicSquareModeCochain d M N' Nc i j w) = 0 := by
  rw [scaledFlatBlockConstraintQCLM, ContinuousLinearMap.smul_apply,
    flatBlockConstraintQCLM_blockPeriodicSquareMode_eq_zero i j hij w,
    smul_zero]

/-! ## Exact flat-Hodge energy of the obstructive sector -/

theorem covariantD1CLM_blockPeriodicSquareModeCochain_apply
    (d M N' Nc : ℕ) [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (i j : Fin d) (w : SUNLieCoord Nc)
    (p : ConcretePlaquette d ((M + M) * N')) :
    covariantD1CLM ρ
        (trivialPhysicalGaugeBackground d ((M + M) * N') Nc)
        (blockPeriodicSquareModeCochain d M N' Nc i j w) p =
      if p.dir1 = i then
        (blockPeriodicSquareSign M N' (p.site j) -
          blockPeriodicSquareSign M N' ((p.site.shift p.dir2) j)) • w
      else if p.dir2 = i then
        (blockPeriodicSquareSign M N' ((p.site.shift p.dir1) j) -
          blockPeriodicSquareSign M N' (p.site j)) • w
      else 0 := by
  rw [covariantD1CLM_trivial_apply]
  simp only [blockPeriodicSquareModeCochain_apply]
  by_cases h1 : p.dir1 = i <;> by_cases h2 : p.dir2 = i
  · exfalso
    have := p.hlt
    omega
  · simp [h1, h2, sub_smul]
  · simp [h1, h2, sub_smul]
  · simp [h1, h2]

theorem gaugeConstraintQCLM_blockPeriodicSquareModeCochain_apply
    (d M N' Nc : ℕ) [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (i j : Fin d) (w : SUNLieCoord Nc)
    (x : FinBox d ((M + M) * N')) :
    gaugeConstraintQCLM ρ
        (trivialPhysicalGaugeBackground d ((M + M) * N') Nc)
        (blockPeriodicSquareModeCochain d M N' Nc i j w) x =
      (blockPeriodicSquareSign M N' (x j) -
        blockPeriodicSquareSign M N' ((x.shiftBack i) j)) • w := by
  rw [gaugeConstraintQCLM_trivial_apply]
  have hterm : ∀ k : Fin d,
      (blockPeriodicSquareModeCochain d M N' Nc i j w (x, k) -
        blockPeriodicSquareModeCochain d M N' Nc i j w (x.shiftBack k, k)) =
      if k = i then
        blockPeriodicSquareSign M N' (x j) • w -
          blockPeriodicSquareSign M N' ((x.shiftBack i) j) • w
      else 0 := by
    intro k
    rw [blockPeriodicSquareModeCochain_apply,
      blockPeriodicSquareModeCochain_apply]
    by_cases hk : k = i
    · subst k
      simp
    · simp [hk]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  rw [Finset.sum_ite_eq' Finset.univ i]
  simp only [Finset.mem_univ, if_true]
  rw [sub_smul]

theorem gaugeConstraintQCLM_blockPeriodicSquareModeCochain_eq_zero_of_ne
    (d M N' Nc : ℕ) [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (i j : Fin d) (hij : i ≠ j)
    (w : SUNLieCoord Nc) :
    gaugeConstraintQCLM ρ
        (trivialPhysicalGaugeBackground d ((M + M) * N') Nc)
        (blockPeriodicSquareModeCochain d M N' Nc i j w) = 0 := by
  apply PiLp.ext
  intro x
  change gaugeConstraintQCLM ρ
      (trivialPhysicalGaugeBackground d ((M + M) * N') Nc)
      (blockPeriodicSquareModeCochain d M N' Nc i j w) x = 0
  rw [gaugeConstraintQCLM_blockPeriodicSquareModeCochain_apply]
  have hcoord : (x.shiftBack i) j = x j := by
    simp [FinBox.shiftBack, Ne.symm hij]
  rw [hcoord, sub_self, zero_smul]

theorem norm_sq_covariantD1CLM_blockPeriodicSquareModeCochain_of_ne
    (d M N' Nc : ℕ) [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (i j : Fin d) (hij : i ≠ j)
    (w : SUNLieCoord Nc) :
    ‖covariantD1CLM ρ
        (trivialPhysicalGaugeBackground d ((M + M) * N') Nc)
        (blockPeriodicSquareModeCochain d M N' Nc i j w)‖ ^ 2 =
      8 * (N' : ℝ) * ((((M + M) * N' : ℕ) : ℝ) ^ (d - 1)) *
        ‖w‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  let D := covariantD1CLM ρ
    (trivialPhysicalGaugeBackground d ((M + M) * N') Nc)
      (blockPeriodicSquareModeCochain d M N' Nc i j w)
  let e := concretePlaquetteEquivOrderedPair d ((M + M) * N')
  have hsplit :
      (∑ p : ConcretePlaquette d ((M + M) * N'), ‖D p‖ ^ 2) =
        ∑ z : FinBox d ((M + M) * N') × OrderedDirectionPair d,
          ‖D (e.symm z)‖ ^ 2 := by
    have h := e.sum_comp (fun z => ‖D (e.symm z)‖ ^ 2)
    simpa using h
  rw [hsplit, Fintype.sum_prod_type]
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · let q0 : OrderedDirectionPair d := ⟨(i, j), hijlt⟩
    have hpoint : ∀ (x : FinBox d ((M + M) * N'))
        (q : OrderedDirectionPair d),
        ‖D (e.symm (x, q))‖ ^ 2 =
          if q = q0 then
            (blockPeriodicSquareSign M N' (x j) -
              blockPeriodicSquareSign M N' ((x.shift j) j)) ^ 2 * ‖w‖ ^ 2
          else 0 := by
      intro x q
      change
        ‖covariantD1CLM ρ
          (trivialPhysicalGaugeBackground d ((M + M) * N') Nc)
          (blockPeriodicSquareModeCochain d M N' Nc i j w)
          ⟨x, q.1.1, q.1.2, q.2⟩‖ ^ 2 = _
      by_cases hq : q = q0
      · subst q
        rw [if_pos rfl,
          covariantD1CLM_blockPeriodicSquareModeCochain_apply]
        simp only [q0, if_pos, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      · rw [if_neg hq,
          covariantD1CLM_blockPeriodicSquareModeCochain_apply]
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
    rw [← Finset.sum_mul,
      sum_finBox_blockPeriodicSquareSign_shift_diff_sq]
  · let q0 : OrderedDirectionPair d := ⟨(j, i), hjilt⟩
    have hpoint : ∀ (x : FinBox d ((M + M) * N'))
        (q : OrderedDirectionPair d),
        ‖D (e.symm (x, q))‖ ^ 2 =
          if q = q0 then
            (blockPeriodicSquareSign M N' (x j) -
              blockPeriodicSquareSign M N' ((x.shift j) j)) ^ 2 * ‖w‖ ^ 2
          else 0 := by
      intro x q
      change
        ‖covariantD1CLM ρ
          (trivialPhysicalGaugeBackground d ((M + M) * N') Nc)
          (blockPeriodicSquareModeCochain d M N' Nc i j w)
          ⟨x, q.1.1, q.1.2, q.2⟩‖ ^ 2 = _
      by_cases hq : q = q0
      · subst q
        rw [if_pos rfl,
          covariantD1CLM_blockPeriodicSquareModeCochain_apply]
        simp only [q0, if_neg (Ne.symm hij), if_pos, norm_smul, mul_pow,
          Real.norm_eq_abs, sq_abs]
        ring
      · rw [if_neg hq,
          covariantD1CLM_blockPeriodicSquareModeCochain_apply]
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
    rw [← Finset.sum_mul,
      sum_finBox_blockPeriodicSquareSign_shift_diff_sq]

theorem flatGaugeHodgeK0_inner_blockPeriodicSquareModeCochain_of_ne
    (d M N' Nc : ℕ) [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (i j : Fin d) (hij : i ≠ j)
    (w : SUNLieCoord Nc) :
    inner ℝ (blockPeriodicSquareModeCochain d M N' Nc i j w)
        (flatGaugeHodgeK0CLM d ((M + M) * N') Nc ρ
          (blockPeriodicSquareModeCochain d M N' Nc i j w)) =
      8 * (N' : ℝ) * ((((M + M) * N' : ℕ) : ℝ) ^ (d - 1)) *
        ‖w‖ ^ 2 := by
  rw [flatGaugeHodgeK0_inner_right]
  rw [norm_sq_covariantD1CLM_blockPeriodicSquareModeCochain_of_ne
      d M N' Nc ρ i j hij w,
    gaugeConstraintQCLM_blockPeriodicSquareModeCochain_eq_zero_of_ne
      d M N' Nc ρ i j hij w,
    norm_zero]
  norm_num

/-! ## Full-volume consequence -/

/-- **Critical all-mode no-go on every positive coarse torus.**  For
`Nc >= 2` and every `N' > 0`, the current full-space critical Poincare gate
is false.  The obstruction is the block-periodic transverse sector above;
its exact Hodge Rayleigh quotient is `8 / L` independently of `N'`. -/
theorem volumeUniformCriticalRescaledFlatPoincareGate_false
    {N' Nc : ℕ} [NeZero N'] [NeZero Nc]
    (hNc : 2 ≤ Nc) (ρ : SUNAdjointModel Nc) :
    ¬ VolumeUniformCriticalRescaledFlatPoincareGate N' Nc ρ := by
  rintro ⟨CP, _hCP, hall⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (8 * CP)
  let M := n + 1
  haveI : NeZero M := ⟨by simp [M]⟩
  let k := (M + M) - 1
  have hk : k + 1 = M + M := by
    dsimp [k]
    omega
  have hP :
      ScaledFlatGaugeHodgePoincare 4 (M + M) N' Nc ρ
        (((M + M : ℕ) : ℝ)) CP := by
    simpa only [hk] using hall k
  have hdim : 0 < Nc ^ 2 - 1 := by
    have h4 : 2 * 2 ≤ Nc * Nc := Nat.mul_le_mul hNc hNc
    have hsq : Nc ^ 2 = Nc * Nc := by ring
    rw [hsq]
    omega
  let w : SUNLieCoord Nc :=
    EuclideanSpace.single (⟨0, hdim⟩ : Fin (Nc ^ 2 - 1)) (1 : ℝ)
  let i : Fin 4 := ⟨0, by omega⟩
  let j : Fin 4 := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j]
  let A : FinePhysicalOneCochain 4 (M + M) N' Nc :=
    blockPeriodicSquareModeCochain 4 M N' Nc i j w
  have hw : ‖w‖ ^ 2 = 1 := by
    dsimp [w]
    rw [EuclideanSpace.norm_single]
    norm_num
  have hnorm :
      ‖A‖ ^ 2 = ((((M + M) * N' : ℕ) : ℝ)) ^ 4 := by
    dsimp [A]
    rw [norm_sq_blockPeriodicSquareModeCochain, hw, mul_one]
  have hH :
      inner ℝ A
          (flatGaugeHodgeK0CLM 4 ((M + M) * N') Nc ρ A) =
        8 * (N' : ℝ) * ((((M + M) * N' : ℕ) : ℝ)) ^ 3 := by
    dsimp [A]
    rw [flatGaugeHodgeK0_inner_blockPeriodicSquareModeCochain_of_ne
      4 M N' Nc ρ i j hij w, hw, mul_one]
  have hQ :
      scaledFlatBlockConstraintQCLM (d := 4) (Nc := Nc)
        (((M + M : ℕ) : ℝ)) A = 0 := by
    dsimp [A]
    exact criticalScaledBlockConstraintQCLM_blockPeriodicSquareMode_eq_zero
      i j hij w
  have hmain := hP.2 A
  rw [hQ, norm_zero, zero_pow (by norm_num), add_zero, hH, hnorm] at hmain
  have hside : (0 : ℝ) < ((((M + M) * N' : ℕ) : ℝ)) := by
    exact_mod_cast Nat.mul_pos (by
      have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
      omega) (Nat.pos_of_ne_zero (NeZero.ne N'))
  have hside3 : (0 : ℝ) < ((((M + M) * N' : ℕ) : ℝ)) ^ 3 :=
    pow_pos hside 3
  have hfac :
      ((((M + M) * N' : ℕ) : ℝ)) *
          ((((M + M) * N' : ℕ) : ℝ)) ^ 3 ≤
        (8 * CP * (N' : ℝ)) *
          ((((M + M) * N' : ℕ) : ℝ)) ^ 3 := by
    convert hmain using 1 <;> ring
  have htotal :
      ((((M + M) * N' : ℕ) : ℝ)) ≤ 8 * CP * (N' : ℝ) :=
    (mul_le_mul_iff_of_pos_right hside3).mp hfac
  have hN' : (0 : ℝ) < (N' : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N')
  have hcancel :
      (((M + M : ℕ) : ℝ)) * (N' : ℝ) ≤
        (8 * CP) * (N' : ℝ) := by
    simpa only [Nat.cast_mul] using htotal
  have hupper : (((M + M : ℕ) : ℝ)) ≤ 8 * CP :=
    (mul_le_mul_iff_of_pos_right hN').mp hcancel
  have hbig : 8 * CP < (((M + M : ℕ) : ℝ)) := by
    dsimp [M]
    push_cast
    linarith
  linarith

end YangMills.RG
