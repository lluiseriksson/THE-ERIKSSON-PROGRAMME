import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
PRE-VALIDATION: production source present; production .olean not yet
materialized and production compiler result not verified. Exact draft
passed HOT ledger1233. Scalar plane-wave algebra only. It does not identify a finite
torus wrap, a boundary mask, the physical precision or its inverse.
-/

namespace YangMills.RG

theorem neumannOppositeExponentialDifference (z c : ℂ) :
    ((Complex.exp (-z) - 1) / c) * ((Complex.exp z - 1) / c) =
      (2 - Complex.exp z - Complex.exp (-z)) / (c * c) := by
  rw [div_mul_div_comm]
  congr 1
  have h : Complex.exp (-z) * Complex.exp z = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  calc
    _ = Complex.exp (-z) * Complex.exp z - Complex.exp z -
        Complex.exp (-z) + 1 := by ring
    _ = _ := by rw [h]; ring

theorem neumannIntegerPlaneWave_centeredDifference (z : ℂ) (k : ℤ) :
    (Complex.exp (z * (k : ℂ)) - Complex.exp (z * ((k + 1 : ℤ) : ℂ))) -
      (Complex.exp (z * ((k - 1 : ℤ) : ℂ)) - Complex.exp (z * (k : ℂ))) =
      (2 - Complex.exp z - Complex.exp (-z)) * Complex.exp (z * (k : ℂ)) := by
  have hp : Complex.exp (z * ((k + 1 : ℤ) : ℂ)) =
      Complex.exp (z * (k : ℂ)) * Complex.exp z := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hm : Complex.exp (z * ((k - 1 : ℤ) : ℂ)) =
      Complex.exp (z * (k : ℂ)) * Complex.exp (-z) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hp, hm]
  ring

end YangMills.RG
