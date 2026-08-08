/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourcePi4Collar
import YangMills.RG.PhysicalShellLocalityDiv

/-!
# The literal CMP99 `Pi^4` collar is a simple domain

This file supplies the topological part of the source collar dictionary.  It
constructs short periodic coordinate arcs without choosing a nonperiodic
ordering of the torus, joins the four coordinate arcs, and proves that the
literal Chebyshev radius-two collar is face-connected.  Thus the printed
`Pi^4` region itself, rather than an unspecified connected subset, becomes a
`CMP99SimpleLocalizationDomain` of size at most `625`.

The short-arc proof treats small tori uniformly: when a nominal shift fixes a
vertex, the corresponding graph walk is the nil walk, so no loop edge is
introduced.
-/

namespace YangMills.RG

noncomputable section

/-- A circular-distance-two coordinate lies at one of the five nominal
positions `a`, `a+1`, `a+2`, `a-1`, `a-2`.  On small tori some positions may
coincide. -/
theorem finTorusDist_le_two_cases {N : ℕ} [NeZero N] (a b : Fin N)
    (h : finTorusDist a b ≤ 2) :
    b = a ∨
    b = ⟨(a.val + 1) % N, Nat.mod_lt _ (NeZero.pos N)⟩ ∨
    b = ⟨(a.val + 2) % N, Nat.mod_lt _ (NeZero.pos N)⟩ ∨
    b = ⟨(a.val + N - 1) % N, Nat.mod_lt _ (NeZero.pos N)⟩ ∨
    b = ⟨(a.val + N - 2) % N, Nat.mod_lt _ (NeZero.pos N)⟩ := by
  unfold finTorusDist zmodCircDist zmodCircVal at h
  rw [neg_sub] at h
  rcases min_le_iff.mp h with h | h
  · have hv : ((a.val : ZMod N) - (b.val : ZMod N)).val = 0 ∨
        ((a.val : ZMod N) - (b.val : ZMod N)).val = 1 ∨
        ((a.val : ZMod N) - (b.val : ZMod N)).val = 2 := by omega
    rcases hv with hv | hv | hv
    · left
      apply finToZMod_injective
      have hz : (a.val : ZMod N) - (b.val : ZMod N) = 0 :=
        (ZMod.val_eq_zero _).mp hv
      exact (sub_eq_zero.mp hz).symm
    · right; right; right; left
      have hN : 1 < N := by
        have := ZMod.val_lt ((a.val : ZMod N) - (b.val : ZMod N))
        omega
      apply finToZMod_injective
      have hz : (a.val : ZMod N) - (b.val : ZMod N) = 1 := by
        apply ZMod.val_injective N
        have hone : (1 : ZMod N).val = 1 := by
          rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hN]
        exact hv.trans hone.symm
      have hb : (b.val : ZMod N) = (a.val : ZMod N) - 1 :=
        (eq_sub_iff_add_eq).2 ((sub_eq_iff_eq_add').1 hz).symm
      change (b.val : ZMod N) = (((a.val + N - 1) % N : ℕ) : ZMod N)
      rw [hb, ZMod.natCast_mod]
      have hsplit : a.val + N - 1 = a.val + (N - 1) := by omega
      rw [hsplit, Nat.cast_add, Nat.cast_sub (NeZero.one_le),
        ZMod.natCast_self, Nat.cast_one]
      ring
    · right; right; right; right
      have hN : 2 < N := by
        have := ZMod.val_lt ((a.val : ZMod N) - (b.val : ZMod N))
        omega
      apply finToZMod_injective
      have hz : (a.val : ZMod N) - (b.val : ZMod N) = 2 := by
        apply ZMod.val_injective N
        have htwo : (2 : ZMod N).val = 2 := by
          rw [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt hN]
        exact hv.trans htwo.symm
      have hb : (b.val : ZMod N) = (a.val : ZMod N) - 2 :=
        (eq_sub_iff_add_eq).2 ((sub_eq_iff_eq_add').1 hz).symm
      change (b.val : ZMod N) = (((a.val + N - 2) % N : ℕ) : ZMod N)
      rw [hb, ZMod.natCast_mod]
      have hsplit : a.val + N - 2 = a.val + (N - 2) := by omega
      rw [hsplit, Nat.cast_add, Nat.cast_sub (by omega : 2 ≤ N),
        ZMod.natCast_self]
      push_cast
      ring

  · have hv : ((b.val : ZMod N) - (a.val : ZMod N)).val = 0 ∨
        ((b.val : ZMod N) - (a.val : ZMod N)).val = 1 ∨
        ((b.val : ZMod N) - (a.val : ZMod N)).val = 2 := by omega
    rcases hv with hv | hv | hv
    · left
      apply finToZMod_injective
      have hz : (b.val : ZMod N) - (a.val : ZMod N) = 0 :=
        (ZMod.val_eq_zero _).mp hv
      exact sub_eq_zero.mp hz
    · right; left
      have hN : 1 < N := by
        have := ZMod.val_lt ((b.val : ZMod N) - (a.val : ZMod N))
        omega
      apply finToZMod_injective
      have hz : (b.val : ZMod N) - (a.val : ZMod N) = 1 := by
        apply ZMod.val_injective N
        have hone : (1 : ZMod N).val = 1 := by
          rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hN]
        exact hv.trans hone.symm
      have hb : (b.val : ZMod N) = (a.val : ZMod N) + 1 :=
        (sub_eq_iff_eq_add').1 hz
      change (b.val : ZMod N) = (((a.val + 1) % N : ℕ) : ZMod N)
      rw [hb, ZMod.natCast_mod]
      push_cast
      ring

    · right; right; left
      have hN : 2 < N := by
        have := ZMod.val_lt ((b.val : ZMod N) - (a.val : ZMod N))
        omega
      apply finToZMod_injective
      have hz : (b.val : ZMod N) - (a.val : ZMod N) = 2 := by
        apply ZMod.val_injective N
        have htwo : (2 : ZMod N).val = 2 := by
          rw [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt hN]
        exact hv.trans htwo.symm
      have hb : (b.val : ZMod N) = (a.val : ZMod N) + 2 :=
        (sub_eq_iff_eq_add').1 hz
      change (b.val : ZMod N) = (((a.val + 2) % N : ℕ) : ZMod N)
      rw [hb, ZMod.natCast_mod]
      push_cast
      ring

/-- Forward and backward cyclic coordinate steps. -/
def cmp99CyclicSucc {N : ℕ} [NeZero N] (a : Fin N) : Fin N :=
  ⟨(a.val + 1) % N, Nat.mod_lt _ (NeZero.pos N)⟩

def cmp99CyclicPred {N : ℕ} [NeZero N] (a : Fin N) : Fin N :=
  ⟨(a.val + N - 1) % N, Nat.mod_lt _ (NeZero.pos N)⟩

theorem cmp99CyclicSucc_cast {N : ℕ} [NeZero N] (a : Fin N) :
    ((cmp99CyclicSucc a).val : ZMod N) = (a.val : ZMod N) + 1 := by
  rw [cmp99CyclicSucc, ZMod.natCast_mod]
  push_cast
  ring

theorem cmp99CyclicPred_cast {N : ℕ} [NeZero N] (a : Fin N) :
    ((cmp99CyclicPred a).val : ZMod N) = (a.val : ZMod N) - 1 := by
  rw [cmp99CyclicPred, ZMod.natCast_mod]
  have hsplit : a.val + N - 1 = a.val + (N - 1) := by omega
  rw [hsplit, Nat.cast_add, Nat.cast_sub (NeZero.one_le),
    ZMod.natCast_self, Nat.cast_one]
  ring

/-- The short-arc alternatives in an iteration-friendly form. -/
theorem finTorusDist_le_two_cyclic_cases {N : ℕ} [NeZero N] (a b : Fin N)
    (h : finTorusDist a b ≤ 2) :
    b = a ∨ b = cmp99CyclicSucc a ∨
      b = cmp99CyclicSucc (cmp99CyclicSucc a) ∨
      b = cmp99CyclicPred a ∨
      b = cmp99CyclicPred (cmp99CyclicPred a) := by
  rcases finTorusDist_le_two_cases a b h with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · right; right; left
    rw [h]
    apply finToZMod_injective
    change ((((a.val + 2) % N : ℕ) : ZMod N)) =
      ((cmp99CyclicSucc (cmp99CyclicSucc a)).val : ZMod N)
    rw [ZMod.natCast_mod, cmp99CyclicSucc_cast, cmp99CyclicSucc_cast]
    push_cast
    ring
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · right; right; right; right
    by_cases hN : N = 1
    · subst N
      exact Subsingleton.elim _ _
    have hN2 : 2 ≤ N := by omega
    rw [h]
    apply finToZMod_injective
    change ((((a.val + N - 2) % N : ℕ) : ZMod N)) =
      ((cmp99CyclicPred (cmp99CyclicPred a)).val : ZMod N)
    rw [ZMod.natCast_mod, cmp99CyclicPred_cast, cmp99CyclicPred_cast]
    have hsplit : a.val + N - 2 = a.val + (N - 2) := by omega
    rw [hsplit, Nat.cast_add, Nat.cast_sub hN2,
      ZMod.natCast_self]
    push_cast
    ring

/-- A one-edge forward walk, with degeneracies on small tori collapsed to a
nil walk. -/
theorem exists_cmp116CoarseFaceShiftWalk {d N : ℕ} [NeZero N]
    (x : FinBox d N) (i : Fin d) :
    ∃ w : (cmp116CoarseFaceAdj d N).Walk x (FinBox.shift x i),
      ∀ v ∈ w.support, v = x ∨ v = FinBox.shift x i := by
  by_cases h : FinBox.shift x i = x
  · rw [h]
    exact ⟨SimpleGraph.Walk.nil, by simp⟩
  · refine ⟨SimpleGraph.Walk.cons
      ⟨fun hxi => h hxi.symm, i, Or.inl rfl⟩ SimpleGraph.Walk.nil, ?_⟩
    simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil]

/-- A one-edge backward walk, again collapsing a periodic degeneracy. -/
theorem exists_cmp116CoarseFaceShiftBackWalk {d N : ℕ} [NeZero N]
    (x : FinBox d N) (i : Fin d) :
    ∃ w : (cmp116CoarseFaceAdj d N).Walk x (FinBox.shiftBack x i),
      ∀ v ∈ w.support, v = x ∨ v = FinBox.shiftBack x i := by
  by_cases h : FinBox.shiftBack x i = x
  · rw [h]
    exact ⟨SimpleGraph.Walk.nil, by simp⟩
  · refine ⟨SimpleGraph.Walk.cons
      ⟨fun hxi => h hxi.symm, i, Or.inr (FinBox.shift_shiftBack x i).symm⟩
      SimpleGraph.Walk.nil, ?_⟩
    simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil]

/-- Replace one coordinate of a periodic box. -/
def cmp99ReplaceCoord {d N : ℕ} (x : FinBox d N) (i : Fin d) (a : Fin N) :
    FinBox d N := fun j => if j = i then a else x j

@[simp] theorem cmp99ReplaceCoord_apply_same {d N : ℕ}
    (x : FinBox d N) (i : Fin d) (a : Fin N) :
    cmp99ReplaceCoord x i a i = a := by simp [cmp99ReplaceCoord]

@[simp] theorem cmp99ReplaceCoord_apply_ne {d N : ℕ}
    (x : FinBox d N) (i j : Fin d) (a : Fin N) (hji : j ≠ i) :
    cmp99ReplaceCoord x i a j = x j := by simp [cmp99ReplaceCoord, hji]

theorem cmp99ReplaceCoord_self {d N : ℕ} (x : FinBox d N) (i : Fin d) :
    cmp99ReplaceCoord x i (x i) = x := by
  funext j
  by_cases hji : j = i <;> simp [cmp99ReplaceCoord, hji]

theorem cmp99ReplaceCoord_succ {d N : ℕ} [NeZero N]
    (x : FinBox d N) (i : Fin d) :
    cmp99ReplaceCoord x i (cmp99CyclicSucc (x i)) = FinBox.shift x i := by
  funext j
  by_cases hji : j = i <;>
    simp [cmp99ReplaceCoord, cmp99CyclicSucc, FinBox.shift, hji]

theorem cmp99ReplaceCoord_pred {d N : ℕ} [NeZero N]
    (x : FinBox d N) (i : Fin d) :
    cmp99ReplaceCoord x i (cmp99CyclicPred (x i)) = FinBox.shiftBack x i := by
  funext j
  by_cases hji : j = i <;>
    simp [cmp99ReplaceCoord, cmp99CyclicPred, FinBox.shiftBack, hji]

theorem cmp99ReplaceCoord_succ_succ {d N : ℕ} [NeZero N]
    (x : FinBox d N) (i : Fin d) :
    cmp99ReplaceCoord x i (cmp99CyclicSucc (cmp99CyclicSucc (x i))) =
      FinBox.shift (FinBox.shift x i) i := by
  funext j
  by_cases hji : j = i
  · subst j
    apply Fin.ext
    simp [cmp99ReplaceCoord, cmp99CyclicSucc, FinBox.shift,
      Nat.mod_add_mod, Nat.add_assoc]
  · simp [cmp99ReplaceCoord, FinBox.shift, hji]

theorem cmp99ReplaceCoord_pred_pred {d N : ℕ} [NeZero N]
    (x : FinBox d N) (i : Fin d) :
    cmp99ReplaceCoord x i (cmp99CyclicPred (cmp99CyclicPred (x i))) =
      FinBox.shiftBack (FinBox.shiftBack x i) i := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [cmp99ReplaceCoord, cmp99CyclicPred, FinBox.shiftBack]
  · simp [cmp99ReplaceCoord, FinBox.shiftBack, hji]

/-- A short face walk changing only coordinate `i`, with its support listed
explicitly among the one- and two-step arc vertices. -/
theorem exists_cmp99ReplaceCoord_shortWalk {d N : ℕ} [NeZero N]
    (x : FinBox d N) (i : Fin d) (a : Fin N)
    (ha : finTorusDist (x i) a ≤ 2) :
    ∃ w : (cmp116CoarseFaceAdj d N).Walk x (cmp99ReplaceCoord x i a),
      ∀ v ∈ w.support,
        v = x ∨
        v = FinBox.shift x i ∨
        v = FinBox.shift (FinBox.shift x i) i ∨
        v = FinBox.shiftBack x i ∨
        v = FinBox.shiftBack (FinBox.shiftBack x i) i := by
  rcases finTorusDist_le_two_cyclic_cases (x i) a ha with h | h | h | h | h
  · rw [h, cmp99ReplaceCoord_self]
    exact ⟨SimpleGraph.Walk.nil, by simp⟩
  · rw [h, cmp99ReplaceCoord_succ]
    obtain ⟨w, hw⟩ := exists_cmp116CoarseFaceShiftWalk x i
    refine ⟨w, ?_⟩
    intro v hv
    rcases hw v hv with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rw [h, cmp99ReplaceCoord_succ_succ]
    obtain ⟨w₁, hw₁⟩ := exists_cmp116CoarseFaceShiftWalk x i
    obtain ⟨w₂, hw₂⟩ := exists_cmp116CoarseFaceShiftWalk (FinBox.shift x i) i
    refine ⟨w₁.append w₂, ?_⟩
    intro v hv
    rw [SimpleGraph.Walk.mem_support_append_iff] at hv
    rcases hv with hv | hv
    · rcases hw₁ v hv with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases hw₂ v hv with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
  · rw [h, cmp99ReplaceCoord_pred]
    obtain ⟨w, hw⟩ := exists_cmp116CoarseFaceShiftBackWalk x i
    refine ⟨w, ?_⟩
    intro v hv
    rcases hw v hv with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rw [h, cmp99ReplaceCoord_pred_pred]
    obtain ⟨w₁, hw₁⟩ := exists_cmp116CoarseFaceShiftBackWalk x i
    obtain ⟨w₂, hw₂⟩ :=
      exists_cmp116CoarseFaceShiftBackWalk (FinBox.shiftBack x i) i
    refine ⟨w₁.append w₂, ?_⟩
    intro v hv
    rw [SimpleGraph.Walk.mem_support_append_iff] at hv
    rcases hv with hv | hv
    · rcases hw₁ v hv with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · rcases hw₂ v hv with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

private theorem mem_pi4_shift_of_coord_eq {Q : ℕ} [NeZero Q]
    (cell x : FinBox 4 Q) (i : Fin 4)
    (hx : x ∈ cmp99SourcePi4CollarCells cell) (hi : x i = cell i) :
    FinBox.shift x i ∈ cmp99SourcePi4CollarCells cell := by
  rw [mem_cmp99SourcePi4CollarCells_iff] at hx ⊢
  unfold finBoxDist at hx ⊢
  apply Finset.sup_le
  intro j _
  by_cases hji : j = i
  · subst j
    have hs := finTorusDist_succ_le (x i)
    simp only [FinBox.shift, if_pos] at hs ⊢
    rw [← hi]
    omega
  · simp only [FinBox.shift, if_neg hji]
    exact (Finset.le_sup (f := fun k => finTorusDist (cell k) (x k))
      (Finset.mem_univ j)).trans hx

private theorem mem_pi4_shift_shift_of_coord_eq {Q : ℕ} [NeZero Q]
    (cell x : FinBox 4 Q) (i : Fin 4)
    (hx : x ∈ cmp99SourcePi4CollarCells cell) (hi : x i = cell i) :
    FinBox.shift (FinBox.shift x i) i ∈
      cmp99SourcePi4CollarCells cell := by
  rw [mem_cmp99SourcePi4CollarCells_iff] at hx ⊢
  unfold finBoxDist at hx ⊢
  apply Finset.sup_le
  intro j _
  by_cases hji : j = i
  · subst j
    have h₁ := finTorusDist_succ_le (x i)
    have h₂ := finTorusDist_succ_le ((FinBox.shift x i) i)
    have htri := finTorusDist_triangle (cell i) ((FinBox.shift x i) i)
      ((FinBox.shift (FinBox.shift x i) i) i)
    simp only [FinBox.shift, if_pos] at h₁ h₂ htri ⊢
    rw [← hi] at htri
    rw [← hi]
    omega
  · simp only [FinBox.shift, if_neg hji]
    exact (Finset.le_sup (f := fun k => finTorusDist (cell k) (x k))
      (Finset.mem_univ j)).trans hx

private theorem mem_pi4_shiftBack_of_coord_eq {Q : ℕ} [NeZero Q]
    (cell x : FinBox 4 Q) (i : Fin 4)
    (hx : x ∈ cmp99SourcePi4CollarCells cell) (hi : x i = cell i) :
    FinBox.shiftBack x i ∈ cmp99SourcePi4CollarCells cell := by
  rw [mem_cmp99SourcePi4CollarCells_iff] at hx ⊢
  unfold finBoxDist at hx ⊢
  apply Finset.sup_le
  intro j _
  by_cases hji : j = i
  · subst j
    have hs := finTorusDist_pred_le (x i)
    simp only [FinBox.shiftBack, if_pos] at hs ⊢
    rw [← hi]
    omega
  · simp only [FinBox.shiftBack, if_neg hji]
    exact (Finset.le_sup (f := fun k => finTorusDist (cell k) (x k))
      (Finset.mem_univ j)).trans hx

private theorem mem_pi4_shiftBack_shiftBack_of_coord_eq {Q : ℕ} [NeZero Q]
    (cell x : FinBox 4 Q) (i : Fin 4)
    (hx : x ∈ cmp99SourcePi4CollarCells cell) (hi : x i = cell i) :
    FinBox.shiftBack (FinBox.shiftBack x i) i ∈
      cmp99SourcePi4CollarCells cell := by
  rw [mem_cmp99SourcePi4CollarCells_iff] at hx ⊢
  unfold finBoxDist at hx ⊢
  apply Finset.sup_le
  intro j _
  by_cases hji : j = i
  · subst j
    have h₁ := finTorusDist_pred_le (x i)
    have h₂ := finTorusDist_pred_le ((FinBox.shiftBack x i) i)
    have htri := finTorusDist_triangle (cell i) ((FinBox.shiftBack x i) i)
      ((FinBox.shiftBack (FinBox.shiftBack x i) i) i)
    simp only [FinBox.shiftBack, if_pos] at h₁ h₂ htri ⊢
    rw [← hi] at htri
    rw [← hi]
    omega
  · simp only [FinBox.shiftBack, if_neg hji]
    exact (Finset.le_sup (f := fun k => finTorusDist (cell k) (x k))
      (Finset.mem_univ j)).trans hx

/-- The intermediate point after replacing the first `n` coordinates of the
center by the corresponding coordinates of `target`. -/
def cmp99Pi4Prefix {Q : ℕ} (cell target : FinBox 4 Q) (n : ℕ) : FinBox 4 Q :=
  fun i => if i.val < n then target i else cell i

theorem cmp99Pi4Prefix_zero {Q : ℕ} (cell target : FinBox 4 Q) :
    cmp99Pi4Prefix cell target 0 = cell := by
  funext i
  simp [cmp99Pi4Prefix]

theorem cmp99Pi4Prefix_four {Q : ℕ} (cell target : FinBox 4 Q) :
    cmp99Pi4Prefix cell target 4 = target := by
  funext i
  simp [cmp99Pi4Prefix, i.isLt]

theorem mem_cmp99Pi4Prefix {Q : ℕ} [NeZero Q]
    (cell target : FinBox 4 Q)
    (htarget : target ∈ cmp99SourcePi4CollarCells cell) (n : ℕ) :
    cmp99Pi4Prefix cell target n ∈ cmp99SourcePi4CollarCells cell := by
  rw [mem_cmp99SourcePi4CollarCells_iff] at htarget ⊢
  unfold finBoxDist at htarget ⊢
  apply Finset.sup_le
  intro i _
  by_cases hi : i.val < n
  · rw [cmp99Pi4Prefix, if_pos hi]
    exact (Finset.le_sup (f := fun j => finTorusDist (cell j) (target j))
      (Finset.mem_univ i)).trans htarget
  · rw [cmp99Pi4Prefix, if_neg hi, finTorusDist_self]
    omega

theorem cmp99Pi4Prefix_next_eq_replace {Q : ℕ}
    (cell target : FinBox 4 Q) (n : ℕ) (hn : n < 4) :
    cmp99Pi4Prefix cell target (n + 1) =
      cmp99ReplaceCoord (cmp99Pi4Prefix cell target n)
        ⟨n, hn⟩ (target ⟨n, hn⟩) := by
  funext j
  by_cases hj : j = ⟨n, hn⟩
  · subst j
    simp [cmp99Pi4Prefix, cmp99ReplaceCoord]
  · have hjval : j.val ≠ n := by
      intro hval
      exact hj (Fin.ext hval)
    by_cases hjn : j.val < n
    · simp [cmp99Pi4Prefix, cmp99ReplaceCoord, hj, hjn,
        Nat.lt_succ_of_lt hjn]
    · have hjnext : ¬ j.val < n + 1 := by omega
      simp [cmp99Pi4Prefix, cmp99ReplaceCoord, hj, hjn, hjnext]

theorem cmp99Pi4Prefix_apply_next {Q : ℕ}
    (cell target : FinBox 4 Q) (n : ℕ) (hn : n < 4) :
    cmp99Pi4Prefix cell target n ⟨n, hn⟩ = cell ⟨n, hn⟩ := by
  simp [cmp99Pi4Prefix]

/-- One coordinate phase of the collar path stays inside the literal
`Pi^4` collar. -/
theorem exists_cmp99Pi4Prefix_stepWalk {Q : ℕ} [NeZero Q]
    (cell target : FinBox 4 Q)
    (htarget : target ∈ cmp99SourcePi4CollarCells cell)
    (n : ℕ) (hn : n < 4) :
    ∃ w : (cmp116CoarseFaceAdj 4 Q).Walk
        (cmp99Pi4Prefix cell target n) (cmp99Pi4Prefix cell target (n + 1)),
      ∀ v ∈ w.support, v ∈ cmp99SourcePi4CollarCells cell := by
  let i : Fin 4 := ⟨n, hn⟩
  let x := cmp99Pi4Prefix cell target n
  have hx : x ∈ cmp99SourcePi4CollarCells cell :=
    mem_cmp99Pi4Prefix cell target htarget n
  have hi : x i = cell i := cmp99Pi4Prefix_apply_next cell target n hn
  have ha : finTorusDist (x i) (target i) ≤ 2 := by
    rw [hi]
    exact (finTorusDist_le_finBoxDist cell target i).trans
      ((mem_cmp99SourcePi4CollarCells_iff cell target).mp htarget)
  obtain ⟨w, hw⟩ := exists_cmp99ReplaceCoord_shortWalk x i (target i) ha
  have hend : cmp99Pi4Prefix cell target (n + 1) =
      cmp99ReplaceCoord x i (target i) :=
    cmp99Pi4Prefix_next_eq_replace cell target n hn
  rw [hend]
  refine ⟨w, ?_⟩
  intro v hv
  rcases hw v hv with h | h | h | h | h
  · simpa [h] using hx
  · simpa [h] using mem_pi4_shift_of_coord_eq cell x i hx hi
  · simpa [h] using mem_pi4_shift_shift_of_coord_eq cell x i hx hi
  · simpa [h] using mem_pi4_shiftBack_of_coord_eq cell x i hx hi
  · simpa [h] using mem_pi4_shiftBack_shiftBack_of_coord_eq cell x i hx hi

/-- Every collar cell is joined to the center by a face walk staying inside
the literal collar. -/
theorem exists_cmp99SourcePi4Collar_walk_from_center {Q : ℕ} [NeZero Q]
    (cell target : FinBox 4 Q)
    (htarget : target ∈ cmp99SourcePi4CollarCells cell) :
    ∃ w : (cmp116CoarseFaceAdj 4 Q).Walk cell target,
      ∀ v ∈ w.support, v ∈ cmp99SourcePi4CollarCells cell := by
  obtain ⟨w₀, hw₀⟩ :=
    exists_cmp99Pi4Prefix_stepWalk cell target htarget 0 (by omega)
  obtain ⟨w₁, hw₁⟩ :=
    exists_cmp99Pi4Prefix_stepWalk cell target htarget 1 (by omega)
  obtain ⟨w₂, hw₂⟩ :=
    exists_cmp99Pi4Prefix_stepWalk cell target htarget 2 (by omega)
  obtain ⟨w₃, hw₃⟩ :=
    exists_cmp99Pi4Prefix_stepWalk cell target htarget 3 (by omega)
  let raw := ((w₀.append w₁).append w₂).append w₃
  let w : (cmp116CoarseFaceAdj 4 Q).Walk cell target :=
    raw.copy (cmp99Pi4Prefix_zero cell target)
      (cmp99Pi4Prefix_four cell target)
  refine ⟨w, ?_⟩
  intro v hv
  have hv' : v ∈ raw.support := by
    simpa [w, SimpleGraph.Walk.support_copy] using hv
  dsimp only [raw] at hv'
  rw [SimpleGraph.Walk.mem_support_append_iff] at hv'
  rcases hv' with hv' | hv'
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hv'
    rcases hv' with hv' | hv'
    · rw [SimpleGraph.Walk.mem_support_append_iff] at hv'
      rcases hv' with hv' | hv'
      · exact hw₀ v hv'
      · exact hw₁ v hv'
    · exact hw₂ v hv'
  · exact hw₃ v hv'

/-- The literal `Pi^4` cell collar is face-connected. -/
theorem walkConnected_cmp99SourcePi4CollarCells {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) :
    walkConnected (cmp116CoarseFaceAdj 4 Q)
      (cmp99SourcePi4CollarCells cell) := by
  exact walkConnected_of_walk_from_root _ _ cell
    (exists_cmp99SourcePi4Collar_walk_from_center cell)

/-- Literal CMP99 `Pi^4` collar as a simple localization domain of printed
size at most `5^4 = 625`. -/
def cmp99SourcePi4CollarDomain {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) :
    CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) 625 where
  blocks := cmp99SourcePi4CollarCells cell
  nonempty := ⟨cell, mem_cmp99SourcePi4CollarCells_self cell⟩
  connected := walkConnected_cmp99SourcePi4CollarCells cell
  card_le := card_cmp99SourcePi4CollarCells_le cell

@[simp] theorem cmp99SourcePi4CollarDomain_blocks {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) :
    (cmp99SourcePi4CollarDomain cell).blocks =
      cmp99SourcePi4CollarCells cell := rfl

end

end YangMills.RG
