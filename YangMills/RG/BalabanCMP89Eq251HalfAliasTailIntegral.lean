import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons

/-!
# Cold-sealed: the finite half-exponent alias tail

Cold compiler validation: exact source checkpoint
`c1cdd849d0117cdf18724ac076cd4a5bbfd67b35` passed the fresh Colab Pro+
CPU/high-RAM focal and exact axiom gate recorded in Verification Ledger
Addendum 1027.

This scratch leaf isolates the only analytic estimate needed for the bare
diagonal branch below CMP89 (2.46).  It is deliberately independent of the
project index dictionaries, so elaboration failures can be reproduced against
the pinned Mathlib alone before the physical finite alias window is attached.
-/

namespace YangMills.RG

noncomputable section

/-- The positive half-exponent tail is bounded by its shifted antitone
integral.  The shift by one avoids the artificial `0 ^ (-1/2)` endpoint. -/
theorem cmp89Eq251HalfAliasPositiveTail_le_integral (N : ℕ) :
    (∑ i ∈ Finset.range N,
        (1 + ((i + 1 : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ))) ≤
      ∫ x in (0 : ℝ)..N, (1 + x) ^ (-(1 / 2 : ℝ)) := by
  have hanti :
      AntitoneOn (fun x : ℝ => (1 + x) ^ (-(1 / 2 : ℝ)))
        (Set.Icc 0 (0 + (N : ℝ))) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos
      (by linarith [hx.1]) (by linarith) (by norm_num)
  simpa [Nat.cast_add, Nat.cast_one] using hanti.sum_le_integral

/-- Exact value of the shifted half-exponent integral. -/
theorem cmp89Eq251HalfAliasIntegral_eq (N : ℕ) :
    (∫ x in (0 : ℝ)..N, (1 + x) ^ (-(1 / 2 : ℝ))) =
      2 * (Real.sqrt (N + 1) - 1) := by
  rw [show (fun x : ℝ => (1 + x) ^ (-(1 / 2 : ℝ))) =
      fun x : ℝ => (x + 1) ^ (-(1 / 2 : ℝ)) by
    funext x
    rw [add_comm]]
  rw [intervalIntegral.integral_comp_add_right
    (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) 1]
  rw [integral_rpow (Or.inl (by norm_num))]
  rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by ring]
  simp only [zero_add, Real.sqrt_eq_rpow, Real.one_rpow]
  ring

end

end YangMills.RG
