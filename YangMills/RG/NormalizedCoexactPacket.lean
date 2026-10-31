import YangMills.RG.CoexactFlatEnergy
import YangMills.RG.PolarizedCharacterWeightDensity

/-! Actual normalized coexact character synthesis. The counting-norm identity
is a Gram/Parseval statement for all coefficients, not a supplied frame
certificate. Weighted packet trace and output density remain separate. -/
namespace YangMills.RG
open scoped BigOperators RealInnerProductSpace

theorem counting_backward_mass_eq_forward {G : Type*} [AddCommGroup G] [Fintype G]
    (f : G → ℂ) (a : G) :
    countingL2Mass (fun x => f x - f (x - a)) = forwardShiftEnergy f a := by
  have h := Equiv.sum_comp (Equiv.addRight a) (fun x : G => ‖f x - f (x - a)‖ ^ 2)
  simpa [countingL2Mass, forwardShiftEnergy] using h.symm

section General
variable {D n Nc : ℕ} [NeZero D] [NeZero n] [NeZero Nc]
variable {I : Type*} [Fintype I]

set_option maxHeartbeats 1200000 in
theorem coexact_characterSynthesis_norm_sq (hNc : 2 ≤ Nc) (i j : Fin D) (hij : i ≠ j)
    (chi : I → AddChar (Fin D → ZMod n) ℂ) (hc : Function.Injective chi)
    (c : I → ℂ) :
    ‖coexactFlatMap hNc i j (characterSynthesis chi c)‖ ^ 2 =
      (n : ℝ)^D * ∑ k, ‖c k‖ ^ 2 *
        (‖chi k (Pi.single i (1 : ZMod n)) - 1‖ ^ 2 +
          ‖chi k (Pi.single j (1 : ZMod n)) - 1‖ ^ 2) := by
  classical
  rw [coexactFlatMap_apply, torusPhysicalEmbed_sub_norm_sq hNc i j hij,
    torusPhysicalEmbed_norm_sq, torusPhysicalEmbed_norm_sq]
  have hback (l : Fin D) :
      torusBackwardDifference l (characterSynthesis chi c) =
        (fun x : Fin D → ZMod n => characterSynthesis chi c x -
          characterSynthesis chi c (x - Pi.single l (1 : ZMod n))) := rfl
  rw [hback j, hback i]
  rw [counting_backward_mass_eq_forward, counting_backward_mass_eq_forward,
    character_synthesis_forwardEnergy chi hc, character_synthesis_forwardEnergy chi hc]
  have hcard : (Fintype.card (Fin D → ZMod n) : ℝ) = (n : ℝ)^D := by simp
  simp only [hcard]
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring
end General

section Positive
variable {d n Nc : ℕ} [NeZero n] [NeZero Nc]

noncomputable def positiveCoexactCharacter (R : ℕ) (k : CoexactPositiveIndex d R) :
    AddChar (Fin (d + 2) → ZMod n) ℂ :=
  torusFourierCharacter (centeredFourierFrequency R (coexactPositiveFourierIndex R k))

theorem positiveCoexactCharacter_injective (R : ℕ) (hR : 2 * R < n) :
    Function.Injective (positiveCoexactCharacter (d := d) (n := n) R) :=
  torusFourierCharacter_injective.comp ((centeredFourierFrequency_injective R hR).comp
    (coexactPositiveFourierIndex_injective R))

noncomputable def positiveCoexactSymbolMass (R : ℕ) (k : CoexactPositiveIndex d R) : ℝ :=
  ‖positiveCoexactCharacter (n := n) R k (Pi.single 0 (1 : ZMod n)) - 1‖ ^ 2 +
    ‖positiveCoexactCharacter (n := n) R k
      (Pi.single (Fin.succ (0 : Fin (d + 1))) (1 : ZMod n)) - 1‖ ^ 2

theorem positiveCoexactSymbolMass_pos (R : ℕ) (hR : 2 * R < n)
    (k : CoexactPositiveIndex d R) : 0 < positiveCoexactSymbolMass (n := n) R k := by
  have hz : positiveCoexactCharacter (n := n) R k
      (Pi.single 0 (1 : ZMod n)) - 1 ≠ 0 := by
    simpa only [positiveCoexactCharacter, coexactPositiveProfile, centeredFourierProfile]
      using coexactPositiveProfile_first_multiplier_ne (n := n) R hR k
  have hp := sq_pos_of_pos (norm_pos_iff.mpr hz)
  unfold positiveCoexactSymbolMass
  nlinarith [sq_nonneg ‖positiveCoexactCharacter (n := n) R k
    (Pi.single (Fin.succ (0 : Fin (d + 1))) (1 : ZMod n)) - 1‖]

noncomputable def positiveCoexactNormalization (R : ℕ)
    (k : CoexactPositiveIndex d R) : ℝ :=
  Real.sqrt ((n : ℝ)^(d + 2) * positiveCoexactSymbolMass (n := n) R k)

theorem positiveCoexactNormalization_pos (R : ℕ) (hR : 2 * R < n)
    (k : CoexactPositiveIndex d R) : 0 < positiveCoexactNormalization (n := n) R k := by
  apply Real.sqrt_pos.mpr
  have hn : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne n))
  exact mul_pos (pow_pos hn _) (positiveCoexactSymbolMass_pos R hR k)

noncomputable def normalizedCoexactSynthesis (hNc : 2 ≤ Nc) (R : ℕ)
    (c : CoexactPositiveIndex d R → ℂ) : PhysicalGaugeOneCochain (d + 2) n Nc :=
  coexactFlatMap hNc (0 : Fin (d + 2)) (Fin.succ (0 : Fin (d + 1)))
    (characterSynthesis (positiveCoexactCharacter (n := n) R)
      (fun k => c k / (positiveCoexactNormalization (n := n) R k : ℂ)))

set_option maxHeartbeats 1200000 in
theorem normalizedCoexactSynthesis_norm_sq (hNc : 2 ≤ Nc) (R : ℕ) (hR : 2 * R < n)
    (c : CoexactPositiveIndex d R → ℂ) :
    ‖normalizedCoexactSynthesis (n := n) hNc R c‖ ^ 2 = ∑ k, ‖c k‖ ^ 2 := by
  classical
  unfold normalizedCoexactSynthesis
  rw [coexact_characterSynthesis_norm_sq hNc 0 (Fin.succ 0) (by simp) _
    (positiveCoexactCharacter_injective R hR)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hn : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne n))
  have hv : 0 < (n : ℝ)^(d + 2) := pow_pos hn _
  have hb := positiveCoexactSymbolMass_pos (n := n) R hR k
  have hsq : positiveCoexactNormalization (n := n) R k ^ 2 =
      (n : ℝ)^(d + 2) * positiveCoexactSymbolMass (n := n) R k :=
    Real.sq_sqrt (le_of_lt (mul_pos hv hb))
  change (n : ℝ)^(d + 2) *
    (‖c k / (positiveCoexactNormalization (n := n) R k : ℂ)‖ ^ 2 *
      positiveCoexactSymbolMass (n := n) R k) = ‖c k‖ ^ 2
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (positiveCoexactNormalization_pos R hR k), div_pow, hsq]
  field_simp [ne_of_gt hv, ne_of_gt hb] <;> ring

theorem normalizedCoexactSynthesis_div_zero (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc)
    (R : ℕ) (c : CoexactPositiveIndex d R → ℂ) :
    gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground (d + 2) n Nc)
      (normalizedCoexactSynthesis (n := n) hNc R c) = 0 :=
  coexactFlatMap_div_zero hNc rho _ _ _
end Positive
end YangMills.RG
