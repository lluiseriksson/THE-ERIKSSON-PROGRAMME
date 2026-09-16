import YangMills.RG.BalabanCMP89NeumannRectangleActiveRegion

/-!
# PRE-VALIDATION: exact directional masks for the actual torus rectangle

Source present; .olean not materialized; not compiler-verified.
The natural arithmetic below is byte-identical to the separately prepared
Mathlib-only repro. Check that repro before elaborating this physical draft.
Non-strict site fit is retained. Full-period directions stay periodic;
proper directions have nonperiodic masks. This does not produce the physical
carrier choice, reflection covariance, a regional inverse or uniform B0.
-/

namespace YangMills.RG

open YangMills

noncomputable section

theorem rectangleForwardMask_nat
    (k h N : ℕ) (hN : 0 < N) (hk : k < h) (hfit : h ≤ N) :
    (k + 1) % N < h ↔ h = N ∨ k + 1 < h := by
  by_cases hh : h = N
  · subst h
    constructor
    · intro _
      exact Or.inl rfl
    · intro _
      exact Nat.mod_lt _ hN
  · rw [Nat.mod_eq_of_lt (by omega : k + 1 < N)]
    omega

theorem rectangleBackwardMask_nat
    (k h N : ℕ) (hN : 0 < N) (hk : k < h) (hfit : h ≤ N) :
    (k + N - 1) % N < h ↔ h = N ∨ 0 < k := by
  by_cases hh : h = N
  · subst h
    constructor
    · intro _
      exact Or.inl rfl
    · intro _
      exact Nat.mod_lt _ hN
  · by_cases hk0 : k = 0
    · subst k
      rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega : N - 1 < N)]
      omega
    · rw [show k + N - 1 = (k - 1) + N by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : k - 1 < N)]
      omega

/-- Outgoing actual internal bonds retain a wrap exactly on full-period sides.
This is a directionwise statement, not an all-directions strict-fit premise. -/
theorem neumannRectangle_outgoingBond_iff
    {N : ℕ} [NeZero N] {m : Fin 4 → ℤ}
    (hm : ∀ mu, 0 < m mu) (hfit : ∀ mu, m mu ≤ (N : ℤ))
    (x : ActiveGaugeRegion.Site
      (cmp89SourceNeumannRectangleActiveRegion (N := N) m))
    (i : Fin 4) :
    (x.1, i) ∈ (cmp89SourceNeumannRectangleActiveRegion (N := N) m).bonds ↔
      Int.toNat (m i) = N ∨ (x.1 i).val + 1 < Int.toNat (m i) := by
  classical
  have hx := (mem_cmp89SourceNeumannRectangleActiveRegion_sites_iff x.1).mp x.2
  have hfitNat : Int.toNat (m i) ≤ N := by
    exact_mod_cast (show (Int.toNat (m i) : ℤ) ≤ (N : ℤ) by
      rw [Int.toNat_of_nonneg (hm i).le]
      exact hfit i)
  have hstep :
      x.1.shift i ∈ (cmp89SourceNeumannRectangleActiveRegion (N := N) m).sites ↔
        ((x.1 i).val + 1) % N < Int.toNat (m i) := by
    rw [mem_cmp89SourceNeumannRectangleActiveRegion_sites_iff]
    constructor
    · intro hall
      simpa only [FinBox.shift, if_pos rfl] using hall i
    · intro hi mu
      by_cases hmu : mu = i
      · subst mu
        simpa only [FinBox.shift, if_pos rfl] using hi
      · simpa only [FinBox.shift, if_neg hmu] using hx mu
  have hbond :
      (x.1, i) ∈ (cmp89SourceNeumannRectangleActiveRegion (N := N) m).bonds ↔
        x.1.shift i ∈ (cmp89SourceNeumannRectangleActiveRegion (N := N) m).sites := by
    simp only [ActiveGaugeRegion.bonds, Finset.mem_filter, Finset.mem_univ,
      true_and, x.2]
  rw [hbond, hstep]
  exact rectangleForwardMask_nat _ _ _ (NeZero.pos N) (hx i) hfitNat

/-- Incoming actual internal bonds retain the wrap into coordinate zero only
on full-period sides. The target identity uses shift_shiftBack explicitly. -/
theorem neumannRectangle_incomingBond_iff
    {N : ℕ} [NeZero N] {m : Fin 4 → ℤ}
    (hm : ∀ mu, 0 < m mu) (hfit : ∀ mu, m mu ≤ (N : ℤ))
    (x : ActiveGaugeRegion.Site
      (cmp89SourceNeumannRectangleActiveRegion (N := N) m))
    (i : Fin 4) :
    (x.1.shiftBack i, i) ∈
        (cmp89SourceNeumannRectangleActiveRegion (N := N) m).bonds ↔
      Int.toNat (m i) = N ∨ 0 < (x.1 i).val := by
  classical
  have hx := (mem_cmp89SourceNeumannRectangleActiveRegion_sites_iff x.1).mp x.2
  have hfitNat : Int.toNat (m i) ≤ N := by
    exact_mod_cast (show (Int.toNat (m i) : ℤ) ≤ (N : ℤ) by
      rw [Int.toNat_of_nonneg (hm i).le]
      exact hfit i)
  have hstep :
      x.1.shiftBack i ∈ (cmp89SourceNeumannRectangleActiveRegion (N := N) m).sites ↔
        ((x.1 i).val + N - 1) % N < Int.toNat (m i) := by
    rw [mem_cmp89SourceNeumannRectangleActiveRegion_sites_iff]
    constructor
    · intro hall
      simpa only [FinBox.shiftBack, if_pos rfl] using hall i
    · intro hi mu
      by_cases hmu : mu = i
      · subst mu
        simpa only [FinBox.shiftBack, if_pos rfl] using hi
      · simpa only [FinBox.shiftBack, if_neg hmu] using hx mu
  have hbond :
      (x.1.shiftBack i, i) ∈
          (cmp89SourceNeumannRectangleActiveRegion (N := N) m).bonds ↔
        x.1.shiftBack i ∈ (cmp89SourceNeumannRectangleActiveRegion (N := N) m).sites := by
    simp only [ActiveGaugeRegion.bonds, Finset.mem_filter, Finset.mem_univ,
      true_and, FinBox.shift_shiftBack, x.2, and_true]
  rw [hbond, hstep]
  exact rectangleBackwardMask_nat _ _ _ (NeZero.pos N) (hx i) hfitNat

#print axioms rectangleForwardMask_nat
#print axioms rectangleBackwardMask_nat
#print axioms neumannRectangle_outgoingBond_iff
#print axioms neumannRectangle_incomingBond_iff

end
end YangMills.RG
