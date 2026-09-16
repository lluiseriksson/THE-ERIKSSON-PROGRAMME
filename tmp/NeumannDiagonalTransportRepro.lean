import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# PRE-VALIDATION: finite diagonal-phase and permutation transport
Source present; .olean not materialized; result not compiler-verified.
Mathlib-only repro. The matrix-entry law is a generic algebraic premise here;
the physical consumer must supply its derived R2 identity, not assume it.
-/

namespace NeumannDiagonalTransportRepro
open scoped BigOperators
noncomputable section

variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]

def transport (p : Equiv.Perm I) (D f : I → K) : I → K :=
  fun k => D (p.symm k) * f (p.symm k)

theorem action (p : Equiv.Perm I) (D : I → K) (hD : ∀ i, D i ≠ 0)
    (A B : Matrix I I K)
    (h : ∀ m n, B (p m) (p n) = D m * A m n * (D n)⁻¹)
    (f : I → K) (m : I) :
    B.mulVec (transport p D f) (p m) = D m * A.mulVec f m := by
  simp only [Matrix.mulVec, dotProduct]
  calc
    (∑ n, B (p m) n * transport p D f n) =
        ∑ n, B (p m) (p n) * transport p D f (p n) :=
      (Equiv.sum_comp p (fun n => B (p m) n * transport p D f n)).symm
    _ = ∑ n, D m * (A m n * f n) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [h]
      simp only [transport, Equiv.symm_apply_apply]
      field_simp [hD n] <;> ring
    _ = D m * ∑ n, A m n * f n := (Finset.mul_sum _ _ _).symm

theorem action_function (p : Equiv.Perm I) (D : I → K)
    (hD : ∀ i, D i ≠ 0) (A B : Matrix I I K)
    (h : ∀ m n, B (p m) (p n) = D m * A m n * (D n)⁻¹)
    (f : I → K) :
    B.mulVec (transport p D f) = transport p D (A.mulVec f) := by
  funext k
  obtain ⟨m, rfl⟩ := p.surjective k
  simpa only [transport, Equiv.symm_apply_apply] using action p D hD A B h f m

theorem solution_unique (p : Equiv.Perm I) (D : I → K)
    (hD : ∀ i, D i ≠ 0) (A B : Matrix I I K)
    (h : ∀ m n, B (p m) (p n) = D m * A m n * (D n)⁻¹)
    (source f g : I → K) (hf : A.mulVec f = source)
    (hg : B.mulVec g = transport p D source)
    (hinj : Function.Injective B.mulVec) :
    transport p D f = g := by
  apply hinj
  rw [action_function p D hD A B h f, hf, hg]

#print axioms action
#print axioms action_function
#print axioms solution_unique

end
end NeumannDiagonalTransportRepro
