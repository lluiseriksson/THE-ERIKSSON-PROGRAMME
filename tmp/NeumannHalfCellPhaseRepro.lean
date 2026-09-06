import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.BigOperators.Intervals

/-!
# PRE-VALIDATION: finite reverse-sum phase, Mathlib-only repro

Source present; .olean not materialized; result not compiler-verified.
This is the phase primitive needed for the actual finite averaging symbol
under a half-cell reflection. It does not prove Green covariance or identify
a regional inverse. No exclusion of c=0 or exp(c)=1 is permitted.
-/

open scoped BigOperators

namespace NeumannHalfCellPhaseRepro

theorem finite_exp_reverse (N : ℕ) (c : ℂ) :
    (∑ k ∈ Finset.range N, Complex.exp (c * (k : ℂ))) =
      Complex.exp (c * ((N - 1 : ℕ) : ℂ)) *
        ∑ k ∈ Finset.range N, Complex.exp (-(c * (k : ℂ))) := by
  calc
    _ = ∑ k ∈ Finset.range N,
        Complex.exp (c * ((N - 1 - k : ℕ) : ℂ)) :=
      (Finset.sum_range_reflect
        (fun k => Complex.exp (c * (k : ℂ))) N).symm
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hkN : k < N := Finset.mem_range.mp hk
      have hsub : k ≤ N - 1 := by omega
      rw [← Complex.exp_add]
      congr 1
      rw [Nat.cast_sub hsub]
      ring

#print axioms finite_exp_reverse

end NeumannHalfCellPhaseRepro
