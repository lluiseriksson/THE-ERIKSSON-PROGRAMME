/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BlockMaps
import YangMills.RG.PhysicalBondDistance

/-!
# Exact torus distance of canonical block basepoints

Multiplication by a block scale embeds the coarse cyclic lattice into the
fine cyclic lattice.  This module proves that circular distance, and hence
Chebyshev box distance, is multiplied by exactly the block scale.  The proof
handles both directed arcs explicitly, so it remains valid across the
periodic seam.
-/

namespace YangMills.RG

/-- Transporting a finite box across equality of side lengths leaves every
underlying coordinate value unchanged. -/
theorem finBox_cast_apply_val
    {d N₁ N₂ : ℕ} (h : N₁ = N₂) (x : FinBox d N₁) (i : Fin d) :
    (((h ▸ x) i).val : ℕ) = (x i).val := by
  subst h
  rfl

/-- Chebyshev torus distance is invariant under a common transport of the
ambient side length. -/
theorem finBoxDist_cast_size
    {d N₁ N₂ : ℕ} (h : N₁ = N₂) (x y : FinBox d N₁) :
    finBoxDist (h ▸ x) (h ▸ y) = finBoxDist x y := by
  subst h
  rfl

/-- The value of a directed cyclic difference commutes with the canonical
scale embedding from `ZMod N` to `ZMod (L*N)`. -/
theorem scaled_fin_sub_val
    (L N : ℕ) [NeZero L] [NeZero N] (a b : Fin N) :
    (((L * a.val : ℕ) : ZMod (L * N)) -
        ((L * b.val : ℕ) : ZMod (L * N))).val =
      L * (((a.val : ℕ) : ZMod N) - ((b.val : ℕ) : ZMod N)).val := by
  have hL : 0 < L := NeZero.pos L
  have haFine : L * a.val < L * N :=
    (Nat.mul_lt_mul_left hL).2 a.isLt
  have hbFine : L * b.val < L * N :=
    (Nat.mul_lt_mul_left hL).2 b.isLt
  have ha : (((a.val : ℕ) : ZMod N)).val = a.val :=
    ZMod.val_cast_of_lt a.isLt
  have hb : (((b.val : ℕ) : ZMod N)).val = b.val :=
    ZMod.val_cast_of_lt b.isLt
  have haF : (((L * a.val : ℕ) : ZMod (L * N))).val = L * a.val :=
    ZMod.val_cast_of_lt haFine
  have hbF : (((L * b.val : ℕ) : ZMod (L * N))).val = L * b.val :=
    ZMod.val_cast_of_lt hbFine
  rcases lt_trichotomy a.val b.val with hab | hab | hab
  · have hne : ((b.val : ℕ) : ZMod N) - (a.val : ℕ) ≠ 0 := by
      intro hzero
      have heq : ((b.val : ℕ) : ZMod N) = (a.val : ℕ) :=
        sub_eq_zero.mp hzero
      have hval := congrArg ZMod.val heq
      rw [hb, ha] at hval
      omega
    letI : NeZero (((b.val : ℕ) : ZMod N) - (a.val : ℕ)) := ⟨hne⟩
    have hneF : ((L * b.val : ℕ) : ZMod (L * N)) -
        (L * a.val : ℕ) ≠ 0 := by
      intro hzero
      have heq : ((L * b.val : ℕ) : ZMod (L * N)) =
          (L * a.val : ℕ) := sub_eq_zero.mp hzero
      have hval := congrArg ZMod.val heq
      rw [hbF, haF] at hval
      exact (Nat.ne_of_gt hab) (Nat.mul_left_cancel hL hval)
    letI : NeZero (((L * b.val : ℕ) : ZMod (L * N)) -
        (L * a.val : ℕ)) := ⟨hneF⟩
    have hba : (((a.val : ℕ) : ZMod N)).val ≤
        (((b.val : ℕ) : ZMod N)).val := by rw [ha, hb]; omega
    have hbaF : (((L * a.val : ℕ) : ZMod (L * N))).val ≤
        (((L * b.val : ℕ) : ZMod (L * N))).val := by rw [haF, hbF]; gcongr
    have hsub : ((((b.val : ℕ) : ZMod N) - (a.val : ℕ))).val =
        b.val - a.val := by rw [ZMod.val_sub hba, hb, ha]
    have hsubF : ((((L * b.val : ℕ) : ZMod (L * N)) -
        (L * a.val : ℕ))).val = L * (b.val - a.val) := by
      rw [ZMod.val_sub hbaF, hbF, haF, Nat.mul_sub_left_distrib]
    calc
      (((L * a.val : ℕ) : ZMod (L * N)) -
          ((L * b.val : ℕ) : ZMod (L * N))).val =
          (-(((L * b.val : ℕ) : ZMod (L * N)) -
            ((L * a.val : ℕ) : ZMod (L * N)))).val := by congr 2 <;> ring
      _ = L * N - (((L * b.val : ℕ) : ZMod (L * N)) -
            ((L * a.val : ℕ) : ZMod (L * N))).val :=
        ZMod.val_neg_of_ne_zero _
      _ = L * (N - (b.val - a.val)) := by
        rw [hsubF]
        exact (Nat.mul_sub_left_distrib L N (b.val - a.val)).symm
      _ = L * (N - ((((b.val : ℕ) : ZMod N) -
            ((a.val : ℕ) : ZMod N))).val) := by rw [hsub]
      _ = L * (-(((b.val : ℕ) : ZMod N) -
            ((a.val : ℕ) : ZMod N))).val := by rw [ZMod.val_neg_of_ne_zero]
      _ = L * (((a.val : ℕ) : ZMod N) -
            ((b.val : ℕ) : ZMod N)).val := by congr 2 <;> ring
  · have habFin : a = b := Fin.ext hab
    subst b
    simp
  · have hba : (((b.val : ℕ) : ZMod N)).val ≤
        (((a.val : ℕ) : ZMod N)).val := by rw [ha, hb]; omega
    have hbaF : (((L * b.val : ℕ) : ZMod (L * N))).val ≤
        (((L * a.val : ℕ) : ZMod (L * N))).val := by rw [haF, hbF]; gcongr
    rw [ZMod.val_sub hbaF, ZMod.val_sub hba, haF, hbF, ha, hb,
      Nat.mul_sub_left_distrib]

/-- Circular torus distance between scaled coordinates is exactly the scale
times the original circular distance. -/
theorem finTorusDist_scaled_fin
    (L N : ℕ) [NeZero L] [NeZero N] (a b : Fin N) :
    finTorusDist
        ⟨L * a.val, (Nat.mul_lt_mul_left (NeZero.pos L)).2 a.isLt⟩
        ⟨L * b.val, (Nat.mul_lt_mul_left (NeZero.pos L)).2 b.isLt⟩ =
      L * finTorusDist a b := by
  unfold finTorusDist zmodCircDist zmodCircVal
  rw [scaled_fin_sub_val L N a b]
  rw [show -(((L * a.val : ℕ) : ZMod (L * N)) -
      ((L * b.val : ℕ) : ZMod (L * N))) =
    (((L * b.val : ℕ) : ZMod (L * N)) -
      ((L * a.val : ℕ) : ZMod (L * N))) by ring]
  rw [show -(((a.val : ℕ) : ZMod N) - ((b.val : ℕ) : ZMod N)) =
    (((b.val : ℕ) : ZMod N) - ((a.val : ℕ) : ZMod N)) by ring]
  rw [scaled_fin_sub_val L N b a]
  exact (mul_min_of_nonneg _ _ (Nat.zero_le L)).symm

/-- Canonical lower block corners multiply the Chebyshev torus distance by
exactly the block scale. -/
theorem finBoxDist_blockBasepoint_eq_mul
    {d : ℕ} (L N : ℕ) [NeZero L] [NeZero N]
    (x y : FinBox d N) :
    finBoxDist (blockBasepoint L N x) (blockBasepoint L N y) =
      L * finBoxDist x y := by
  unfold finBoxDist
  simp only [blockBasepoint]
  simp_rw [finTorusDist_scaled_fin]
  generalize (Finset.univ : Finset (Fin d)) = s
  induction s using Finset.induction with
  | empty => simp
  | @insert a s _ ih =>
      simp only [Finset.sup_insert, ih]
      exact (mul_max_of_nonneg _ _ (Nat.zero_le L)).symm

end YangMills.RG
