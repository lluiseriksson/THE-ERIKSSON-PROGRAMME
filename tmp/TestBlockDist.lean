import YangMills.RG.BlockMaps
import YangMills.RG.PhysicalBondDistance

namespace YangMills.RG

theorem scaled_fin_sub_val
    (L N : ℕ) [NeZero L] [NeZero N] (a b : Fin N) :
    (((L * a.val : ℕ) : ZMod (L * N)) -
        ((L * b.val : ℕ) : ZMod (L * N))).val =
      L * (((a.val : ℕ) : ZMod N) - ((b.val : ℕ) : ZMod N)).val := by
  have hL : 0 < L := NeZero.pos L
  have hN : 0 < N := NeZero.pos N
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
      have heq : ((b.val : ℕ) : ZMod N) = (a.val : ℕ) := sub_eq_zero.mp hzero
      have := congrArg ZMod.val heq
      rw [hb, ha] at this
      omega
    letI : NeZero (((b.val : ℕ) : ZMod N) - (a.val : ℕ)) := ⟨hne⟩
    have hneF : ((L * b.val : ℕ) : ZMod (L * N)) -
        (L * a.val : ℕ) ≠ 0 := by
      intro hzero
      have heq : ((L * b.val : ℕ) : ZMod (L * N)) =
          (L * a.val : ℕ) := sub_eq_zero.mp hzero
      have := congrArg ZMod.val heq
      rw [hbF, haF] at this
      exact (Nat.ne_of_gt hab) (Nat.mul_left_cancel hL this)
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
  | @insert a s ha ih =>
      simp only [Finset.sup_insert, ih]
      exact (mul_max_of_nonneg _ _ (Nat.zero_le L)).symm

end YangMills.RG
