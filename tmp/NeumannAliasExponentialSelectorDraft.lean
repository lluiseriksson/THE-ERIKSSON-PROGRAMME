import YangMills.RG.NeumannCenteredAliasCharacter

/-!
PRE-VALIDATION: source present; .olean not materialized and compiler result
not verified. Literal positive exponential phases are transported to the
sealed centered-alias character sum. The result selects congruence, not an
infinite-lattice point source. No alias-negation symmetry is assumed.
-/

namespace YangMills.RG
noncomputable section

theorem neumannIntegerVectorCharacter_phase
    (d N : ℕ) [NeZero N] (m u : Fin d → ℤ) :
    cmp99FlatZModFourierCharacter (fun i => (m i : ZMod N))
      (fun i => (u i : ZMod N)) =
      Complex.exp (∑ i, 2 * Real.pi * Complex.I *
        (m i : ℂ) * (u i : ℂ) / (N : ℂ)) := by
  rw [Complex.exp_sum]
  unfold cmp99FlatZModFourierCharacter
  apply Finset.prod_congr rfl
  intro i _
  exact neumannIntegerCharacter_product_phase N (m i) (u i)

theorem neumannCenteredAlias_exponential_sum
    (d N : ℕ) [NeZero N] (u : Fin d → ℤ) :
    (∑ m : {m : Fin d → ℤ // m ∈ cmp89Eq245CenteredAliasVectors d N},
      Complex.exp (∑ i, 2 * Real.pi * Complex.I *
        (m.1 i : ℂ) * (u i : ℂ) / (N : ℂ))) =
      if (fun i => (u i : ZMod N)) = (0 : CMP99FlatZModBox d N)
      then (N : ℂ)^d else 0 := by
  calc
    _ = ∑ m : {m : Fin d → ℤ // m ∈ cmp89Eq245CenteredAliasVectors d N},
        cmp99FlatZModFourierCharacter (fun i => (m.1 i : ZMod N))
          (fun i => (u i : ZMod N)) := by
      apply Finset.sum_congr rfl
      intro m _
      exact (neumannIntegerVectorCharacter_phase d N m.1 u).symm
    _ = _ := neumannCenteredAlias_character_sum d N (fun i => (u i : ZMod N))

theorem neumannCenteredAlias_shiftedPhase_sum
    (d N : ℕ) [NeZero N] (z : Fin d → ℂ) (u : Fin d → ℤ) :
    (∑ m : {m : Fin d → ℤ // m ∈ cmp89Eq245CenteredAliasVectors d N},
      Complex.exp (∑ i, Complex.I *
        (z i + 2 * Real.pi * (m.1 i : ℂ)) * (u i : ℂ) / (N : ℂ))) =
      Complex.exp (∑ i, Complex.I * z i * (u i : ℂ) / (N : ℂ)) *
        (if (fun i => (u i : ZMod N)) = (0 : CMP99FlatZModBox d N)
         then (N : ℂ)^d else 0) := by
  rw [← neumannCenteredAlias_exponential_sum d N u, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [← Complex.exp_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

end
end YangMills.RG

#print axioms YangMills.RG.neumannIntegerVectorCharacter_phase
#print axioms YangMills.RG.neumannCenteredAlias_exponential_sum
#print axioms YangMills.RG.neumannCenteredAlias_shiftedPhase_sum
