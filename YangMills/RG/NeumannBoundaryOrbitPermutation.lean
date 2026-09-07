import YangMills.RG.BalabanCMP89NeumannReflectionOrbitAlgebra
import Mathlib.Tactic.Ring

/-!
Fixed-source image-index permutation.
Cold-compiled at source 0f43fbdc51650fb2e8d77282d1c3af18b7f406f0.
Independent evidence verification: ledger Addendum 1203 (2026-09-07).
This is only orbit algebra for the existing printed image definition.
No Green covariance, summability, seam, or regional inverse is assumed.
-/

namespace YangMills.RG

/-- Boundary c*m reverses the integer translate and flips parity.
The original source n is not part of this permutation and remains fixed. -/
def neumannBoundaryOrbitIndexEquiv (c : ℤ) : (ℤ × Bool) ≃ (ℤ × Bool) where
  toFun p := (c - p.1, !p.2)
  invFun p := (c - p.1, !p.2)
  left_inv := by
    rintro ⟨k, b⟩
    apply Prod.ext <;> simp
  right_inv := by
    rintro ⟨k, b⟩
    apply Prod.ext <;> simp

theorem neumannBoundaryOrbitIndexEquiv_involutive (c : ℤ) :
    Function.Involutive (neumannBoundaryOrbitIndexEquiv c) := by
  rintro ⟨k, b⟩
  change (c - (c - k), !(!b)) = (k, b)
  apply Prod.ext <;> simp

/-- c=0 is the lower boundary and c=1 the upper boundary.
The side m and source n are unchanged; no positivity is needed for algebra. -/
theorem neumannBoundaryOrbitIndexEquiv_image (c m n : ℤ) (p : ℤ × Bool) :
    2 * c * m - 1 - cmp89NeumannReflectionOrbit m n p.1 p.2 =
      cmp89NeumannReflectionOrbit m n
        (neumannBoundaryOrbitIndexEquiv c p).1
        (neumannBoundaryOrbitIndexEquiv c p).2 := by
  rcases p with ⟨k, b⟩
  cases b <;> simp [neumannBoundaryOrbitIndexEquiv,
    cmp89NeumannReflectionOrbit] <;> ring

end YangMills.RG
