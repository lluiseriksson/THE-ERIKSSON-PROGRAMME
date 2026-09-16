import NeumannCoordinateAliasReflectionDraft
import YangMills.RG.BalabanCMP99SourceAliasReflectionCoefficients

/-!
# PRE-VALIDATION: one-coordinate momentum carry for the physical alias fibre

Source present; .olean not materialized; result not compiler-verified.
The input alias permutation is the R1 diagnostic object with N=L^j.
This supplies the actual wrapped momentum equation and fine-symbol symmetry,
not a free Green covariance. The averaging column/row phases remain separate.
-/

namespace YangMills.RG
noncomputable section

def neumannMomentumCoordinateReflection (d : ℕ) (mu : Fin d)
    (z : Fin d → ℂ) : Fin d → ℂ :=
  fun nu => if nu = mu then -z nu else z nu

theorem neumannMomentumCoordinateReflection_involutive
    (d : ℕ) (mu : Fin d) (z : Fin d → ℂ) :
    neumannMomentumCoordinateReflection d mu
      (neumannMomentumCoordinateReflection d mu z) = z := by
  funext nu
  by_cases h : nu = mu <;> simp [neumannMomentumCoordinateReflection, h]

theorem neumannPhysicalAliasCoordinateReflection_momentum
    (d L j : ℕ) [NeZero L] (mu : Fin d) (z : Fin d → ℂ)
    (m : CMP89Eq246AliasIndex d L j) :
    ∃ w : Fin d → ℤ,
      (∀ nu, nu ≠ mu → w nu = 0) ∧
      cmp89Eq248EntireAliasMomentum
        (neumannMomentumCoordinateReflection d mu z)
        (neumannPhysicalAliasCoordinateReflection d L j mu m).1 =
      fun nu =>
        neumannMomentumCoordinateReflection d mu
          (cmp89Eq248EntireAliasMomentum z m.1) nu +
        (w nu : ℂ) * (((2 * Real.pi * ((L ^ j : ℕ) : ℝ) : ℝ) : ℂ)) := by
  letI : NeZero (L ^ j) := ⟨pow_ne_zero j (NeZero.ne L)⟩
  have hdiv : ((L ^ j : ℕ) : ℤ) ∣
      (neumannPhysicalAliasCoordinateReflection d L j mu m).1 mu + m.1 mu := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    change
      ((neumannAliasCoordinateReflection d (L ^ j) mu m).1 mu : ZMod (L ^ j)) +
        (m.1 mu : ZMod (L ^ j)) = 0
    rw [neumannAliasCoordinateReflection_residue]
    ring
  obtain ⟨k, hk⟩ := hdiv
  refine ⟨fun nu => if nu = mu then k else 0, ?_, ?_⟩
  · intro nu hnu
    simp [hnu]
  · funext nu
    by_cases hnu : nu = mu
    · subst nu
      have hkC := congrArg (fun x : ℤ => (x : ℂ)) hk
      push_cast at hkC
      simp only [cmp89Eq248EntireAliasMomentum, cmp89Eq245AliasShift,
        neumannMomentumCoordinateReflection, if_pos rfl]
      push_cast
      ring_nf at hkC ⊢
      linear_combination (2 * (Real.pi : ℂ)) * hkC
    · have hm :
          (neumannPhysicalAliasCoordinateReflection d L j mu m).1 nu = m.1 nu := by
        exact neumannAliasCoordinateReflection_other d (L ^ j) mu nu hnu m
      simp [cmp89Eq248EntireAliasMomentum, cmp89Eq245AliasShift,
        neumannMomentumCoordinateReflection, hnu, hm]

theorem neumannEntireScaledLaplacianSymbol_coordinateReflection
    (d : ℕ) (mu : Fin d) (xi mass : ℝ) (z : Fin d → ℂ) :
    cmp89Eq245EntireScaledLaplacianSymbol d xi mass
      (neumannMomentumCoordinateReflection d mu z) =
    cmp89Eq245EntireScaledLaplacianSymbol d xi mass z := by
  unfold cmp89Eq245EntireScaledLaplacianSymbol
  congr 1
  apply Finset.sum_congr rfl
  intro nu _
  by_cases hnu : nu = mu
  · simp only [neumannMomentumCoordinateReflection, hnu, if_pos rfl, neg_neg]
    ring
  · simp [neumannMomentumCoordinateReflection, hnu]

theorem neumannEntireAliasFineSymbol_coordinateReflection
    (d L j : ℕ) [NeZero L] (mu : Fin d) (mass : ℝ) (z : Fin d → ℂ)
    (m : CMP89Eq246AliasIndex d L j) :
    cmp89Eq246EntireAliasFineSymbol d L j mass
      (neumannMomentumCoordinateReflection d mu z)
      (neumannPhysicalAliasCoordinateReflection d L j mu m) =
    cmp89Eq246EntireAliasFineSymbol d L j mass z m := by
  obtain ⟨w, _, hw⟩ :=
    neumannPhysicalAliasCoordinateReflection_momentum d L j mu z m
  unfold cmp89Eq246EntireAliasFineSymbol
  rw [hw]
  have hp := cmp89Eq245EntireScaledLaplacianSymbol_add_int_aliasPeriods
    (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j) mass
    (neumannMomentumCoordinateReflection d mu
      (cmp89Eq248EntireAliasMomentum z m.1)) w
  have hs := neumannEntireScaledLaplacianSymbol_coordinateReflection
    d mu (((L ^ j : ℕ) : ℝ)⁻¹) mass (cmp89Eq248EntireAliasMomentum z m.1)
  simpa only [Nat.cast_pow] using hp.trans hs

#print axioms neumannMomentumCoordinateReflection_involutive
#print axioms neumannPhysicalAliasCoordinateReflection_momentum
#print axioms neumannEntireScaledLaplacianSymbol_coordinateReflection
#print axioms neumannEntireAliasFineSymbol_coordinateReflection

end
end YangMills.RG
