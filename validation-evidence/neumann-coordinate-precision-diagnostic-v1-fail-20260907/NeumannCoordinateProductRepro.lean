import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# PRE-VALIDATION: one changed factor in a finite product
Source present; .olean not materialized; result not compiler-verified.
Mathlib-only preflight for the actual coordinate averaging phase.
-/

namespace NeumannCoordinateProductRepro
open scoped BigOperators

theorem one_factor {I A : Type*} [Fintype I] [DecidableEq I]
    [CommMonoid A] (mu : I) (f g : I → A) (c : A)
    (hother : ∀ nu, nu ≠ mu → g nu = f nu) (hmu : g mu = c * f mu) :
    (∏ nu, g nu) = c * ∏ nu, f nu := by
  have he : (∏ nu ∈ Finset.univ.erase mu, g nu) =
      ∏ nu ∈ Finset.univ.erase mu, f nu := by
    apply Finset.prod_congr rfl
    intro nu hnu
    exact hother nu (Finset.mem_erase.mp hnu).1
  calc
    (∏ nu, g nu) = (∏ nu ∈ Finset.univ.erase mu, g nu) * g mu :=
      (Finset.prod_erase_mul Finset.univ g (Finset.mem_univ mu)).symm
    _ = (∏ nu ∈ Finset.univ.erase mu, f nu) * (c * f mu) := by rw [he, hmu]
    _ = c * ((∏ nu ∈ Finset.univ.erase mu, f nu) * f mu) := mul_left_comm _ _ _
    _ = c * ∏ nu, f nu := by
      rw [Finset.prod_erase_mul Finset.univ f (Finset.mem_univ mu)]

#print axioms one_factor
end NeumannCoordinateProductRepro
