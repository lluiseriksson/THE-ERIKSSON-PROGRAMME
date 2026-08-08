/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceCellDomains

/-!
# The literal CMP99 `Pi^4` collar

CMP99 Sect. C defines `Pi^n` to have side `2 + 2n` large blocks.  Because one
source partition cell `Pi` has side two large blocks, `Pi^4` is exactly five
source cells per coordinate: the Chebyshev radius-two collar on the source
cell torus.  This file defines that collar and proves the volume-uniform bound
`5^4 = 625`.

The proof first sharpens the elementary circular-coordinate ball count from
`2(R+1)` to `2R+1`; the center is counted only once.  The product bound then
gives `(2R+1)^d` for `finBoxDist` balls.

Important source boundary: `Pi^5` has odd large-block boundaries and is not
this cell collar.  The source uses it for a separate containment of `Omega_0`.
No claim about `Pi^5`, face-connectivity, or physical range protection is made
in this module.
-/

namespace YangMills.RG

noncomputable section

/-- Sharp volume-independent cardinality bound for a circular coordinate
ball.  The forward arc contains the center and has at most `R+1` points; the
strictly noncentral backward arc has at most `R`. -/
theorem finTorusDist_ball_card_le_two_mul_add_one
    {N : ℕ} [NeZero N] (a : Fin N) (R : ℕ) :
    (Finset.univ.filter (fun b : Fin N => finTorusDist a b ≤ R)).card ≤
      2 * R + 1 := by
  classical
  set Fwd : Finset (Fin N) :=
    Finset.univ.filter
      (fun b : Fin N => ((a.val : ZMod N) - (b.val : ZMod N)).val ≤ R) with hFwd
  set Bwd : Finset (Fin N) :=
    Finset.univ.filter
      (fun b : Fin N => b ≠ a ∧
        ((b.val : ZMod N) - (a.val : ZMod N)).val ≤ R) with hBwd
  have hsub : Finset.univ.filter (fun b : Fin N => finTorusDist a b ≤ R)
      ⊆ Fwd ∪ Bwd := by
    intro b hb
    rw [Finset.mem_filter] at hb
    have hmin : min ((a.val : ZMod N) - (b.val : ZMod N)).val
        ((b.val : ZMod N) - (a.val : ZMod N)).val ≤ R := by
      have h := hb.2
      unfold finTorusDist zmodCircDist zmodCircVal at h
      rwa [neg_sub] at h
    rw [Finset.mem_union]
    rcases min_le_iff.mp hmin with h | h
    · left
      rw [hFwd, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, h⟩
    · by_cases hba : b = a
      · subst b
        left
        rw [hFwd, Finset.mem_filter]
        simp
      · right
        rw [hBwd, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hba, h⟩
  have hFwd_card : Fwd.card ≤ R + 1 := by
    have hinj : Set.InjOn (fun b : Fin N =>
        ((a.val : ZMod N) - (b.val : ZMod N)).val) Fwd := by
      intro b _ b' _ hbb'
      have heq : (a.val : ZMod N) - (b.val : ZMod N) =
          (a.val : ZMod N) - (b'.val : ZMod N) :=
        ZMod.val_injective N hbb'
      exact finToZMod_injective (sub_right_inj.mp heq)
    have hmaps : ∀ b ∈ Fwd, (fun b : Fin N =>
        ((a.val : ZMod N) - (b.val : ZMod N)).val) b ∈
          Finset.range (R + 1) := by
      intro b hb
      rw [hFwd, Finset.mem_filter] at hb
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le hb.2)
    calc
      Fwd.card ≤ (Finset.range (R + 1)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
      _ = R + 1 := Finset.card_range _
  have hBwd_pos : ∀ b ∈ Bwd,
      0 < ((b.val : ZMod N) - (a.val : ZMod N)).val := by
    intro b hb
    rw [hBwd, Finset.mem_filter] at hb
    have hneZ : (b.val : ZMod N) - (a.val : ZMod N) ≠ 0 := by
      intro hzero
      have hcast : (b.val : ZMod N) = (a.val : ZMod N) :=
        sub_eq_zero.mp hzero
      exact hb.2.1 (finToZMod_injective hcast)
    exact Nat.pos_of_ne_zero ((ZMod.val_ne_zero _).2 hneZ)
  have hBwd_card : Bwd.card ≤ R := by
    have hinj : Set.InjOn (fun b : Fin N =>
        ((b.val : ZMod N) - (a.val : ZMod N)).val - 1) Bwd := by
      intro b hb b' hb' hbb'
      have hbpos := hBwd_pos b hb
      have hb'pos := hBwd_pos b' hb'
      dsimp only at hbb'
      have hval : ((b.val : ZMod N) - (a.val : ZMod N)).val =
          ((b'.val : ZMod N) - (a.val : ZMod N)).val := by
        omega
      have heq : (b.val : ZMod N) - (a.val : ZMod N) =
          (b'.val : ZMod N) - (a.val : ZMod N) :=
        ZMod.val_injective N hval
      exact finToZMod_injective (sub_left_inj.mp heq)
    have hmaps : ∀ b ∈ Bwd, (fun b : Fin N =>
        ((b.val : ZMod N) - (a.val : ZMod N)).val - 1) b ∈
          Finset.range R := by
      intro b hb
      have hpos := hBwd_pos b hb
      rw [hBwd, Finset.mem_filter] at hb
      rw [Finset.mem_range]
      dsimp only
      omega
    calc
      Bwd.card ≤ (Finset.range R).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
      _ = R := Finset.card_range _
  calc
    (Finset.univ.filter (fun b : Fin N => finTorusDist a b ≤ R)).card ≤
        (Fwd ∪ Bwd).card := Finset.card_le_card hsub
    _ ≤ Fwd.card + Bwd.card := Finset.card_union_le _ _
    _ ≤ (R + 1) + R := Nat.add_le_add hFwd_card hBwd_card
    _ = 2 * R + 1 := by ring

/-- Sharp product bound for Chebyshev balls on a periodic `FinBox`. -/
theorem finBoxDist_ball_card_le_two_mul_add_one_pow
    {d N : ℕ} [NeZero N] (a : FinBox d N) (R : ℕ) :
    (Finset.univ.filter (fun b : FinBox d N => finBoxDist a b ≤ R)).card ≤
      (2 * R + 1) ^ d := by
  classical
  have hsub : Finset.univ.filter
      (fun b : FinBox d N => finBoxDist a b ≤ R) ⊆
      Fintype.piFinset (fun i =>
        Finset.univ.filter (fun b : Fin N => finTorusDist (a i) b ≤ R)) := by
    intro b hb
    rw [Finset.mem_filter] at hb
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _,
      (finTorusDist_le_finBoxDist a b i).trans hb.2⟩
  calc
    (Finset.univ.filter (fun b : FinBox d N => finBoxDist a b ≤ R)).card ≤
        (Fintype.piFinset (fun i =>
          Finset.univ.filter
            (fun b : Fin N => finTorusDist (a i) b ≤ R))).card :=
      Finset.card_le_card hsub
    _ = ∏ i : Fin d,
        (Finset.univ.filter
          (fun b : Fin N => finTorusDist (a i) b ≤ R)).card :=
      Fintype.card_piFinset _
    _ ≤ ∏ _i : Fin d, (2 * R + 1) :=
      Finset.prod_le_prod' (fun i _ =>
        finTorusDist_ball_card_le_two_mul_add_one (a i) R)
    _ = (2 * R + 1) ^ d := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Literal CMP99 `Pi^4` collar: five source cells per coordinate, centered at
the owning source cell. -/
noncomputable def cmp99SourcePi4CollarCells {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) : Finset (FinBox 4 Q) :=
  Finset.univ.filter fun other => finBoxDist cell other ≤ 2

@[simp] theorem mem_cmp99SourcePi4CollarCells_iff {Q : ℕ} [NeZero Q]
    (cell other : FinBox 4 Q) :
    other ∈ cmp99SourcePi4CollarCells cell ↔
      finBoxDist cell other ≤ 2 := by
  simp [cmp99SourcePi4CollarCells]

/-- The central source cell lies in its own `Pi^4` collar. -/
theorem mem_cmp99SourcePi4CollarCells_self {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) :
    cell ∈ cmp99SourcePi4CollarCells cell := by
  rw [mem_cmp99SourcePi4CollarCells_iff, finBoxDist_self]
  omega

/-- The printed `5^4` volume is a uniform upper bound even on small periodic
tori where wraparound may identify nominal collar cells. -/
theorem card_cmp99SourcePi4CollarCells_le {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) :
    (cmp99SourcePi4CollarCells cell).card ≤ 625 := by
  simpa [cmp99SourcePi4CollarCells] using
    (finBoxDist_ball_card_le_two_mul_add_one_pow cell 2)

end

end YangMills.RG
