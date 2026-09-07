import NeumannBoundaryOrbitPermutationRepro

/-!
# PRE-VALIDATION: fixed-source coordinate permutation of the image family
Source present; .olean not materialized; result not compiler-verified.
The original source n remains fixed. Only translation/parity indices move.
This algebra does not assert Green covariance, convergence or a seam.
-/

namespace YangMills.RG

def neumannBoundaryImageIndexEquiv {d : ℕ} (mu : Fin d) (c : ℤ) :
    ((Fin d → ℤ) × (Fin d → Bool)) ≃ ((Fin d → ℤ) × (Fin d → Bool)) where
  toFun p := ((fun i => if i = mu then c - p.1 i else p.1 i),
    (fun i => if i = mu then !(p.2 i) else p.2 i))
  invFun p := ((fun i => if i = mu then c - p.1 i else p.1 i),
    (fun i => if i = mu then !(p.2 i) else p.2 i))
  left_inv := by
    intro p
    apply Prod.ext <;> funext i <;> by_cases hi : i = mu <;> simp [hi]
  right_inv := by
    intro p
    apply Prod.ext <;> funext i <;> by_cases hi : i = mu <;> simp [hi]

theorem neumannBoundaryImageIndexEquiv_involutive
    {d : ℕ} (mu : Fin d) (c : ℤ) :
    Function.Involutive (neumannBoundaryImageIndexEquiv mu c) := by
  intro p
  apply Prod.ext <;> funext i <;> by_cases hi : i = mu <;>
    simp [neumannBoundaryImageIndexEquiv, hi]

theorem neumannBoundaryImageIndexEquiv_image
    {d : ℕ} (mu : Fin d) (c : ℤ) (m n : Fin d → ℤ)
    (p : (Fin d → ℤ) × (Fin d → Bool)) :
    (fun i => if i = mu then
        2 * c * m mu - 1 - cmp89NeumannReflectionImage m n p.1 p.2 i
      else cmp89NeumannReflectionImage m n p.1 p.2 i) =
      cmp89NeumannReflectionImage m n
        (neumannBoundaryImageIndexEquiv mu c p).1
        (neumannBoundaryImageIndexEquiv mu c p).2 := by
  funext i
  by_cases hi : i = mu
  · subst i
    simpa [cmp89NeumannReflectionImage, neumannBoundaryImageIndexEquiv,
      neumannBoundaryOrbitIndexEquiv] using
      neumannBoundaryOrbitIndexEquiv_image c (m mu) (n mu) (p.1 mu, p.2 mu)
  · simp [cmp89NeumannReflectionImage, neumannBoundaryImageIndexEquiv, hi]

end YangMills.RG

#print axioms YangMills.RG.neumannBoundaryImageIndexEquiv_involutive
#print axioms YangMills.RG.neumannBoundaryImageIndexEquiv_image
