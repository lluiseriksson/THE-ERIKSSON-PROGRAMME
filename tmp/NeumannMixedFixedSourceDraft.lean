import YangMills.RG.NeumannMixedCoordinateCoverage

/-!
PRE-VALIDATION: source present; .olean not materialized and compiler result
not verified. Fixed-source injectivity only, not full-family surjectivity.
FULL has translation alone; PROPER has translation and the reflection bit.
The physical carrier must determine full and m in a subsequent dictionary.
No Green identity, norm budget, uniform B0 or window15 conclusion.
-/

namespace YangMills.RG

def neumannMixedFixedCoordinateIndex (full : Bool) : Type :=
  match full with
  | true => ℤ
  | false => ℤ × Bool

def neumannMixedInsertSource (full : Bool) (m : ℤ)
    (n : neumannImageIntervalPoint m) :
    neumannMixedFixedCoordinateIndex full → neumannMixedCoordinateIndex full m :=
  match full with
  | true => fun k => (k, n)
  | false => fun p => (p.1, p.2, n)

theorem neumannMixedInsertSource_injective (full : Bool) (m : ℤ)
    (n : neumannImageIntervalPoint m) :
    Function.Injective (neumannMixedInsertSource full m n) := by
  cases full
  · intro p q he
    change (p.1, p.2, n) = (q.1, q.2, n) at he
    exact Prod.ext (congrArg (fun a : ℤ × Bool × neumannImageIntervalPoint m => a.1) he)
      (congrArg (fun a : ℤ × Bool × neumannImageIntervalPoint m => a.2.1) he)
  · intro k l he
    change (k, n) = (l, n) at he
    exact congrArg Prod.fst he

def neumannMixedFixedSourceImage {d : ℕ}
    (full : Fin d → Bool) (m : Fin d → ℤ)
    (n : ∀ mu : Fin d, neumannImageIntervalPoint (m mu))
    (p : ∀ mu : Fin d, neumannMixedFixedCoordinateIndex (full mu)) :
    Fin d → ℤ :=
  fun mu => neumannMixedCoordinateImage (full mu) (m mu)
    (neumannMixedInsertSource (full mu) (m mu) (n mu) (p mu))

theorem neumannMixedFixedSourceImage_injective {d : ℕ}
    (full : Fin d → Bool) (m : Fin d → ℤ) (hm : ∀ mu, 0 < m mu)
    (n : ∀ mu : Fin d, neumannImageIntervalPoint (m mu)) :
    Function.Injective (neumannMixedFixedSourceImage full m n) := by
  intro p q he
  funext mu
  have hi := congrFun he mu
  exact neumannMixedInsertSource_injective (full mu) (m mu) (n mu)
    ((neumannMixedCoordinateImage_bijective (full mu) (m mu) (hm mu)).1 hi)

theorem neumannMixedFixedSourceDifference_injective {d : ℕ}
    (full : Fin d → Bool) (m : Fin d → ℤ) (hm : ∀ mu, 0 < m mu)
    (n : ∀ mu : Fin d, neumannImageIntervalPoint (m mu)) (x : Fin d → ℤ) :
    Function.Injective (fun p => x - neumannMixedFixedSourceImage full m n p) := by
  intro p q he
  apply neumannMixedFixedSourceImage_injective full m hm n
  funext mu
  have hi := congrFun he mu
  change x mu - neumannMixedFixedSourceImage full m n p mu =
    x mu - neumannMixedFixedSourceImage full m n q mu at hi
  omega

end YangMills.RG

#print axioms YangMills.RG.neumannMixedInsertSource_injective
#print axioms YangMills.RG.neumannMixedFixedSourceImage_injective
#print axioms YangMills.RG.neumannMixedFixedSourceDifference_injective
