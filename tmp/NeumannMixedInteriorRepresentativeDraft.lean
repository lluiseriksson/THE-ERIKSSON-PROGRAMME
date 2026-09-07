import YangMills.RG.NeumannMixedCoordinateCoverage

/-!
PRE-VALIDATION: source present; .olean not materialized; not compiler-verified.
Explicit interior representative of the varying-source image bijection.
This excludes images of a different interior source without assuming only
fixed-source injectivity. No operator interchange or inverse is claimed.
-/

namespace YangMills.RG

def neumannMixedInteriorRepresentative (full : Bool) (m : ℤ)
    (x : neumannImageIntervalPoint m) : neumannMixedCoordinateIndex full m :=
  match full with
  | true => (0, x)
  | false => (0, false, x)

theorem neumannMixedInteriorRepresentative_image (full : Bool) (m : ℤ)
    (x : neumannImageIntervalPoint m) :
    neumannMixedCoordinateImage full m
      (neumannMixedInteriorRepresentative full m x) = x.1 := by
  cases full <;>
    simp [neumannMixedInteriorRepresentative, neumannMixedCoordinateImage,
      cmp89NeumannReflectionOrbit_false]

theorem neumannMixedCoordinateImage_eq_interior_iff
    (full : Bool) (m : ℤ) (hm : 0 < m)
    (x : neumannImageIntervalPoint m)
    (p : neumannMixedCoordinateIndex full m) :
    neumannMixedCoordinateImage full m p = x.1 ↔
      p = neumannMixedInteriorRepresentative full m x := by
  constructor
  · intro h
    apply (neumannMixedCoordinateImage_bijective full m hm).1
    exact h.trans (neumannMixedInteriorRepresentative_image full m x).symm
  · rintro rfl
    exact neumannMixedInteriorRepresentative_image full m x

theorem neumannMixedFamilyImage_eq_interior_iff {d : ℕ}
    (full : Fin d → Bool) (m : Fin d → ℤ) (hm : ∀ mu, 0 < m mu)
    (x : ∀ mu, neumannImageIntervalPoint (m mu))
    (p : ∀ mu, neumannMixedCoordinateIndex (full mu) (m mu)) :
    (fun mu => neumannMixedCoordinateImage (full mu) (m mu) (p mu)) =
        (fun mu => (x mu).1) ↔
      p = (fun mu => neumannMixedInteriorRepresentative (full mu) (m mu) (x mu)) := by
  constructor
  · intro h
    funext mu
    exact (neumannMixedCoordinateImage_eq_interior_iff
      (full mu) (m mu) (hm mu) (x mu) (p mu)).1 (congrFun h mu)
  · rintro rfl
    funext mu
    exact neumannMixedInteriorRepresentative_image (full mu) (m mu) (x mu)

#print axioms neumannMixedInteriorRepresentative_image
#print axioms neumannMixedCoordinateImage_eq_interior_iff
#print axioms neumannMixedFamilyImage_eq_interior_iff

end YangMills.RG
