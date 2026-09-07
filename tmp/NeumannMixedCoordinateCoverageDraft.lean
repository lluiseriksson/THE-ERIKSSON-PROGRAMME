import YangMills.RG.NeumannPeriodicIntervalCoverage
import Mathlib.Logic.Equiv.Prod

/-!
PRE-VALIDATION: draft source present; .olean not materialized and compiler
result not verified. M1 coordinate assembly only, not a physical dictionary.
FULL classification is explicit data here; the regional carrier producer
must later fix it from equality with the ambient side, not choose it freely.
FULL has one periodic branch. PROPER retains exactly the sealed Bool pair.
Positive sides refer to the half-open original site interval in both cases.
No summability, inverse, uniform B0 or window15 claim.
-/

namespace YangMills.RG

def neumannMixedCoordinateIndex (full : Bool) (m : ℤ) : Type :=
  match full with
  | true => ℤ × neumannImageIntervalPoint m
  | false => ℤ × Bool × neumannImageIntervalPoint m

def neumannMixedCoordinateImage (full : Bool) (m : ℤ) :
    neumannMixedCoordinateIndex full m → ℤ :=
  match full with
  | true => fun p => p.2.1 + m * p.1
  | false => fun p => cmp89NeumannReflectionOrbit m p.2.2.1 p.1 p.2.1

theorem neumannMixedCoordinateImage_bijective
    (full : Bool) (m : ℤ) (hm : 0 < m) :
    Function.Bijective (neumannMixedCoordinateImage full m) := by
  cases full
  · exact neumannImageIntervalFamily_bijective m hm
  · exact neumannPeriodicIntervalFamily_bijective m hm

noncomputable def neumannMixedCoordinateEquiv
    (full : Bool) (m : ℤ) (hm : 0 < m) :
    neumannMixedCoordinateIndex full m ≃ ℤ :=
  Equiv.ofBijective (neumannMixedCoordinateImage full m)
    (neumannMixedCoordinateImage_bijective full m hm)

noncomputable def neumannMixedCoordinateFamilyEquiv {d : ℕ}
    (full : Fin d → Bool) (m : Fin d → ℤ) (hm : ∀ mu, 0 < m mu) :
    (∀ mu : Fin d, neumannMixedCoordinateIndex (full mu) (m mu)) ≃
      (Fin d → ℤ) :=
  Equiv.piCongrRight (fun mu : Fin d =>
    neumannMixedCoordinateEquiv (full mu) (m mu) (hm mu))

theorem neumannMixedCoordinateFamilyEquiv_apply {d : ℕ}
    (full : Fin d → Bool) (m : Fin d → ℤ) (hm : ∀ mu, 0 < m mu)
    (p : ∀ mu : Fin d, neumannMixedCoordinateIndex (full mu) (m mu))
    (mu : Fin d) :
    neumannMixedCoordinateFamilyEquiv full m hm p mu =
      neumannMixedCoordinateImage (full mu) (m mu) (p mu) := rfl

theorem neumannMixedCoordinateFamily_bijective {d : ℕ}
    (full : Fin d → Bool) (m : Fin d → ℤ) (hm : ∀ mu, 0 < m mu) :
    Function.Bijective (fun p : ∀ mu : Fin d,
      neumannMixedCoordinateIndex (full mu) (m mu) =>
        fun mu : Fin d => neumannMixedCoordinateImage (full mu) (m mu) (p mu)) :=
  (neumannMixedCoordinateFamilyEquiv full m hm).bijective

end YangMills.RG

#print axioms YangMills.RG.neumannMixedCoordinateImage_bijective
#print axioms YangMills.RG.neumannMixedCoordinateEquiv
#print axioms YangMills.RG.neumannMixedCoordinateFamilyEquiv
#print axioms YangMills.RG.neumannMixedCoordinateFamilyEquiv_apply
#print axioms YangMills.RG.neumannMixedCoordinateFamily_bijective
