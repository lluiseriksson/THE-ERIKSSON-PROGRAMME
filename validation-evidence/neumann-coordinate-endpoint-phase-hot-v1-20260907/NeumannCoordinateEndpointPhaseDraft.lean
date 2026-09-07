import NeumannCoordinateAveragePhaseDraft
import YangMills.RG.BalabanCMP99SourceFlatQprimeEndpointAliasPhase

/-!
# PRE-VALIDATION: literal integer endpoint reflection phases

Source present; .olean not materialized; result not compiler-verified.
The reflection is about (N-1)/2 in fine integer coordinates, with physical
spacing N^-1. Wrapped alias periods cancel only at these integer endpoints.
This is phase algebra, not a Green identity or a production seal.
-/

namespace YangMills.RG
noncomputable section

def neumannFineEndpointCoordinateReflection (d N : ℕ) (mu : Fin d)
    (u : Fin d → ℤ) : Fin d → ℤ :=
  fun nu => if nu = mu then ((N - 1 : ℕ) : ℤ) - u nu else u nu

theorem neumannFineEndpointCoordinateReflection_involutive
    (d N : ℕ) (mu : Fin d) (u : Fin d → ℤ) :
    neumannFineEndpointCoordinateReflection d N mu
      (neumannFineEndpointCoordinateReflection d N mu u) = u := by
  funext nu
  by_cases h : nu = mu <;> simp [neumannFineEndpointCoordinateReflection, h]

theorem neumannCoordinateEndpointPhase_identity
    (d N : ℕ) (mu : Fin d) (q : Fin d → ℂ) (u : Fin d → ℤ) :
    cmp89Eq251EntirePhase (neumannMomentumCoordinateReflection d mu q)
      (cmp89Eq249PhysicalFineLatticeDisplacement ((N : ℝ)⁻¹)
        (neumannFineEndpointCoordinateReflection d N mu u)) =
    cmp89Eq251EntirePhase q
      (cmp89Eq249PhysicalFineLatticeDisplacement ((N : ℝ)⁻¹) u) -
      (N : ℂ)⁻¹ * q mu * ((N - 1 : ℕ) : ℂ) := by
  unfold cmp89Eq251EntirePhase
  have hterm (nu : Fin d) :
      neumannMomentumCoordinateReflection d mu q nu *
        ((cmp89Eq249PhysicalFineLatticeDisplacement ((N : ℝ)⁻¹)
          (neumannFineEndpointCoordinateReflection d N mu u) nu : ℝ) : ℂ) =
      q nu * ((cmp89Eq249PhysicalFineLatticeDisplacement ((N : ℝ)⁻¹) u nu : ℝ) : ℂ) -
        (if nu = mu then (N : ℂ)⁻¹ * q mu * ((N - 1 : ℕ) : ℂ) else 0) := by
    by_cases h : nu = mu
    · subst nu
      simp only [neumannMomentumCoordinateReflection,
        neumannFineEndpointCoordinateReflection, if_pos rfl,
        cmp89Eq249PhysicalFineLatticeDisplacement]
      push_cast
      ring
    · simp [neumannMomentumCoordinateReflection,
        neumannFineEndpointCoordinateReflection,
        cmp89Eq249PhysicalFineLatticeDisplacement, h]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib]
  simp

theorem neumannAliasTargetPhase_coordinateReflection
    (d L j : ℕ) [NeZero L] (mu : Fin d) (z : Fin d → ℂ)
    (m : CMP89Eq246AliasIndex d L j) (u : Fin d → ℤ) :
    Complex.exp (Complex.I * cmp89Eq251EntirePhase
      (cmp89Eq248EntireAliasMomentum (neumannMomentumCoordinateReflection d mu z)
        (neumannPhysicalAliasCoordinateReflection d L j mu m).1)
      (cmp89Eq249PhysicalFineLatticeDisplacement (((L ^ j : ℕ) : ℝ)⁻¹)
        (neumannFineEndpointCoordinateReflection d (L ^ j) mu u))) =
    Complex.exp (Complex.I * cmp89Eq251EntirePhase
      (cmp89Eq248EntireAliasMomentum z m.1)
      (cmp89Eq249PhysicalFineLatticeDisplacement (((L ^ j : ℕ) : ℝ)⁻¹) u)) *
      (neumannCoordinateHalfCellPhase d (L ^ j) mu
        (cmp89Eq248EntireAliasMomentum z m.1))⁻¹ := by
  letI : NeZero (L ^ j) := ⟨pow_ne_zero j (NeZero.ne L)⟩
  obtain ⟨w, _, hw⟩ := neumannPhysicalAliasCoordinateReflection_momentum d L j mu z m
  rw [hw, exp_I_cmp89Eq251EntirePhase_add_int_aliasPeriods_physicalFine,
    neumannCoordinateEndpointPhase_identity, mul_sub, Complex.exp_sub]
  simp only [neumannCoordinateHalfCellPhase, div_eq_mul_inv]
  congr 2 <;> congr 1 <;> ring

theorem neumannAliasSourcePhase_coordinateReflection
    (d L j : ℕ) [NeZero L] (mu : Fin d) (z : Fin d → ℂ)
    (m : CMP89Eq246AliasIndex d L j) (u : Fin d → ℤ) :
    Complex.exp (-Complex.I * cmp89Eq251EntirePhase
      (cmp89Eq248EntireAliasMomentum (neumannMomentumCoordinateReflection d mu z)
        (neumannPhysicalAliasCoordinateReflection d L j mu m).1)
      (cmp89Eq249PhysicalFineLatticeDisplacement (((L ^ j : ℕ) : ℝ)⁻¹)
        (neumannFineEndpointCoordinateReflection d (L ^ j) mu u))) =
    Complex.exp (-Complex.I * cmp89Eq251EntirePhase
      (cmp89Eq248EntireAliasMomentum z m.1)
      (cmp89Eq249PhysicalFineLatticeDisplacement (((L ^ j : ℕ) : ℝ)⁻¹) u)) *
      neumannCoordinateHalfCellPhase d (L ^ j) mu
        (cmp89Eq248EntireAliasMomentum z m.1) := by
  have h := congrArg (fun c : ℂ => c⁻¹)
    (neumannAliasTargetPhase_coordinateReflection d L j mu z m u)
  simpa [neg_mul, Complex.exp_neg, mul_comm] using h

#print axioms neumannFineEndpointCoordinateReflection_involutive
#print axioms neumannCoordinateEndpointPhase_identity
#print axioms neumannAliasTargetPhase_coordinateReflection
#print axioms neumannAliasSourcePhase_coordinateReflection

end
end YangMills.RG
