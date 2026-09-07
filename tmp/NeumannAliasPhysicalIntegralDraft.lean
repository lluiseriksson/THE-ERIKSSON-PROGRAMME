import YangMills.RG.NeumannAliasExponentialSelector
import YangMills.RG.NeumannPhysicalBrillouinCharacter

/-!
PRE-VALIDATION: source draft present, .olean not materialized and compiler
result not verified. Compose the literal finite alias selector with the
normalized physical Brillouin integral. The surviving N^4 is explicit;
this is neither an inverse equation nor a density/counting identification.
-/

open MeasureTheory

namespace YangMills.RG
noncomputable section

theorem neumannZeroResidue_exists_integerQuotient
    (d N : ℕ) (u : Fin d → ℤ)
    (hu : (fun i => (u i : ZMod N)) = (0 : CMP99FlatZModBox d N)) :
    ∃ v : Fin d → ℤ, ∀ i, u i = (N : ℤ) * v i := by
  have hd : ∀ i, (N : ℤ) ∣ u i := by
    intro i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (u i) N).mp
    exact congrFun hu i
  choose v hv using hd
  exact ⟨v, hv⟩

theorem neumannIntegerQuotient_phase
    (d N : ℕ) [NeZero N] (z : Fin d → ℂ) (u v : Fin d → ℤ)
    (hv : ∀ i, u i = (N : ℤ) * v i) :
    (∑ i, Complex.I * z i * (u i : ℂ) / (N : ℂ)) =
      Complex.I * (∑ i, z i * (v i : ℂ)) := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hv i, Int.cast_mul, Int.cast_natCast]
  field_simp <;> ring

theorem neumannIntegerQuotient_zero_iff
    (d N : ℕ) [NeZero N] (u v : Fin d → ℤ)
    (hv : ∀ i, u i = (N : ℤ) * v i) : u = 0 ↔ v = 0 := by
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  constructor
  · intro hu
    funext i
    have hmul : (N : ℤ) * v i = 0 := by
      rw [← hv i, hu]
      rfl
    exact (mul_eq_zero.mp hmul).resolve_left hN
  · intro hz
    funext i
    rw [hv i, hz]
    simp

theorem neumannCenteredAlias_physicalIntegral
    (N : ℕ) [NeZero N] (u : Fin 4 → ℤ) :
    cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
      (fun x => ∑ m : {m : Fin 4 → ℤ // m ∈ cmp89Eq245CenteredAliasVectors 4 N},
        Complex.exp (∑ i, Complex.I *
          ((cmp89Eq251PhysicalBrillouinParameter x i : ℂ) +
            2 * Real.pi * (m.1 i : ℂ)) * (u i : ℂ) / (N : ℂ))) =
      if u = 0 then (N : ℂ)^4 else 0 := by
  classical
  have hs (x : Fin 4 → ℝ) := neumannCenteredAlias_shiftedPhase_sum 4 N
    (fun i => (cmp89Eq251PhysicalBrillouinParameter x i : ℂ)) u
  by_cases hz : (fun i => (u i : ZMod N)) = (0 : CMP99FlatZModBox 4 N)
  · obtain ⟨v, hv⟩ := neumannZeroResidue_exists_integerQuotient 4 N u hz
    have hf : (fun x => ∑ m : {m : Fin 4 → ℤ // m ∈ cmp89Eq245CenteredAliasVectors 4 N},
        Complex.exp (∑ i, Complex.I *
          ((cmp89Eq251PhysicalBrillouinParameter x i : ℂ) +
            2 * Real.pi * (m.1 i : ℂ)) * (u i : ℂ) / (N : ℂ))) =
        (fun x => Complex.exp (Complex.I *
          (∑ i, (cmp89Eq251PhysicalBrillouinParameter x i : ℂ) *
            (v i : ℂ))) * (N : ℂ)^4) := by
      funext x
      rw [hs x, if_pos hz, neumannIntegerQuotient_phase 4 N _ u v hv]
    rw [hf]
    have hscale (f : (Fin 4 → ℝ) → ℂ) (c : ℂ) :
        cmp89Eq249NormalizedFourDimensionalBrillouinIntegral (fun x => f x * c) =
          cmp89Eq249NormalizedFourDimensionalBrillouinIntegral f * c := by
      unfold cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
      dsimp only
      rw [integral_mul_const, mul_assoc]
    rw [hscale, neumannPhysicalBrillouin_integerCharacterIntegral]
    by_cases hv0 : v = 0
    · have hu0 := (neumannIntegerQuotient_zero_iff 4 N u v hv).mpr hv0
      simp [hv0, hu0]
    · have hu0 : u ≠ 0 := fun h => hv0
        ((neumannIntegerQuotient_zero_iff 4 N u v hv).mp h)
      simp [hv0, hu0]
  · have hu : u ≠ 0 := by
      intro hu
      apply hz
      subst u
      funext i
      simp
    have hf : (fun x => ∑ m : {m : Fin 4 → ℤ // m ∈ cmp89Eq245CenteredAliasVectors 4 N},
        Complex.exp (∑ i, Complex.I *
          ((cmp89Eq251PhysicalBrillouinParameter x i : ℂ) +
            2 * Real.pi * (m.1 i : ℂ)) * (u i : ℂ) / (N : ℂ))) =
        (fun _ => (0 : ℂ)) := by
      funext x
      rw [hs x, if_neg hz, mul_zero]
    rw [hf, if_neg hu]
    simp [cmp89Eq249NormalizedFourDimensionalBrillouinIntegral]

end
end YangMills.RG

#print axioms YangMills.RG.neumannZeroResidue_exists_integerQuotient
#print axioms YangMills.RG.neumannIntegerQuotient_phase
#print axioms YangMills.RG.neumannIntegerQuotient_zero_iff
#print axioms YangMills.RG.neumannCenteredAlias_physicalIntegral
