import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring

/-!
# finite reverse-sum phase, Mathlib-only repro

Cold compiler/audit verified at source 84ceb5f2 (2026-09-07).
Evidence and scope: VERIFICATION-LEDGER Addendum 1197; no terminal claim.
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
      have hsub : k ≤ N - 1 := Nat.le_sub_one_of_lt hkN
      rw [← Complex.exp_add]
      congr 1
      rw [Nat.cast_sub hsub]
      ring


end NeumannHalfCellPhaseRepro
