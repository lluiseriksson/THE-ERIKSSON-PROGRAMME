/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The ordered noncommutative derivative of the exponential

CMP98 (32)--(33) uses the left-trivialized derivative of the matrix
exponential.  Mathlib's derivative theorem away from zero is stated for a
commutative Banach algebra, so it cannot be used for the matrix algebra in
that equation.

This file first constructs the derivative in an arbitrary real Banach
algebra directly from the exponential power series.  The derivative of the
`n`-th term is the ordered insertion sum

`H |-> (1 / n!) * sum i < n, Y^(n-1-i) * H * Y^i`.

The subsequent CMP98 module will left-trivialize this operator and identify
it with Balaban's series

`g(ad Y) = sum n, (-1)^n/(n+1)! (ad Y)^n`.
-/

namespace YangMills.RG

open scoped BigOperators RightActions

noncomputable section

variable {𝔸 : Type*}
variable [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- The derivative of the `n`-th exponential power-series term, packaged as
a continuous real-linear map. -/
noncomputable def expTermFDeriv (Y : 𝔸) (n : ℕ) : 𝔸 →L[ℝ] 𝔸 :=
  ((n.factorial : ℝ)⁻¹) •
    ∑ i ∈ Finset.range n,
      Y ^ (n.pred - i) •> ContinuousLinearMap.id ℝ 𝔸 <• Y ^ i

/-- Pointwise form of the ordered insertion derivative. -/
theorem expTermFDeriv_apply (Y H : 𝔸) (n : ℕ) :
    expTermFDeriv Y n H =
      ((n.factorial : ℝ)⁻¹) • ∑ i ∈ Finset.range n,
        Y ^ (n.pred - i) * H * Y ^ i := by
  simp [expTermFDeriv]

/-- Each exponential summand has the exact ordered noncommutative
derivative defined above. -/
theorem hasFDerivAt_invFactorial_smul_pow
    (Y : 𝔸) (n : ℕ) :
    HasFDerivAt
      (fun Z : 𝔸 => ((n.factorial : ℝ)⁻¹) • Z ^ n)
      (expTermFDeriv Y n) Y := by
  simpa [expTermFDeriv] using
    ((hasFDerivAt_pow' (𝕜 := ℝ) n (x := Y)).const_smul
      ((n.factorial : ℝ)⁻¹))

/-- Uniform pointwise majorant for one exponential derivative term. -/
theorem norm_expTermFDeriv_apply_le [NormOneClass 𝔸]
    (Y H : 𝔸) (n : ℕ) :
    ‖expTermFDeriv Y n H‖ ≤
      ((n : ℝ) / n.factorial) * ‖Y‖ ^ n.pred * ‖H‖ := by
  rw [expTermFDeriv_apply, norm_smul, Real.norm_eq_abs]
  have hfac : 0 ≤ ((n.factorial : ℝ)⁻¹) := by positivity
  rw [abs_of_nonneg hfac]
  calc
    ((n.factorial : ℝ)⁻¹) *
        ‖∑ i ∈ Finset.range n, Y ^ (n.pred - i) * H * Y ^ i‖
        ≤ ((n.factorial : ℝ)⁻¹) *
          ∑ i ∈ Finset.range n,
            ‖Y ^ (n.pred - i) * H * Y ^ i‖ := by
          gcongr
          exact norm_sum_le _ _
    _ ≤ ((n.factorial : ℝ)⁻¹) *
          ∑ _i ∈ Finset.range n, (‖Y‖ ^ n.pred * ‖H‖) := by
        gcongr with i hi
        have hin : i < n := Finset.mem_range.mp hi
        have hle : i ≤ n.pred := Nat.le_pred_of_lt hin
        calc
          ‖Y ^ (n.pred - i) * H * Y ^ i‖
              ≤ (‖Y ^ (n.pred - i)‖ * ‖H‖) * ‖Y ^ i‖ := by
                exact (norm_mul_le _ _).trans
                  (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
          _ ≤ (‖Y‖ ^ (n.pred - i) * ‖H‖) * ‖Y‖ ^ i := by
                gcongr
                · exact norm_pow_le _ _
                · exact norm_pow_le _ _
          _ = ‖Y‖ ^ n.pred * ‖H‖ := by
                calc
                  ‖Y‖ ^ (n.pred - i) * ‖H‖ * ‖Y‖ ^ i =
                      (‖Y‖ ^ (n.pred - i) * ‖Y‖ ^ i) * ‖H‖ := by ring
                  _ = ‖Y‖ ^ ((n.pred - i) + i) * ‖H‖ := by rw [pow_add]
                  _ = ‖Y‖ ^ n.pred * ‖H‖ := by rw [Nat.sub_add_cancel hle]
    _ = ((n : ℝ) / n.factorial) * ‖Y‖ ^ n.pred * ‖H‖ := by
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm]

/-- Operator-norm version of the exponential derivative majorant. -/
theorem norm_expTermFDeriv_le [NormOneClass 𝔸]
    (Y : 𝔸) (n : ℕ) :
    ‖expTermFDeriv Y n‖ ≤
      ((n : ℝ) / n.factorial) * ‖Y‖ ^ n.pred := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro H
  simpa [mul_assoc] using norm_expTermFDeriv_apply_le Y H n

/-- The derivative majorants are summable on every bounded ball.  Unlike
the Mercator derivative, no radius restriction is needed. -/
theorem summable_natCast_div_factorial_mul_pow_pred (r : ℝ) :
    Summable (fun n : ℕ => ((n : ℝ) / n.factorial) * r ^ n.pred) := by
  rw [← summable_nat_add_iff 1]
  convert Real.summable_pow_div_factorial r using 1
  funext n
  simp only [Nat.pred_succ, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hnpos : 0 < (n : ℝ) + 1 := by positivity
  have hn : (n : ℝ) + 1 ≠ 0 := hnpos.ne'
  field_simp

/- **General noncommutative exponential derivative.**  In an arbitrary
real Banach algebra the derivative of `exp` is the absolutely convergent
sum of all ordered insertion derivatives. -/
set_option maxHeartbeats 2000000 in
theorem hasFDerivAt_exp_ordered [NormOneClass 𝔸] (Y : 𝔸) :
    HasFDerivAt (NormedSpace.exp : 𝔸 → 𝔸)
      (∑' n : ℕ, expTermFDeriv Y n) Y := by
  let r : ℝ := ‖Y‖ + 1
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hYr : ‖Y‖ < r := by dsimp [r]; linarith
  have hu : Summable
      (fun n : ℕ => ((n : ℝ) / n.factorial) * r ^ n.pred) :=
    summable_natCast_div_factorial_mul_pow_pred r
  have hbound : ∀ n (Z : 𝔸), Z ∈ Metric.ball (0 : 𝔸) r →
      ‖expTermFDeriv Z n‖ ≤
        ((n : ℝ) / n.factorial) * r ^ n.pred := by
    intro n Z hZ
    have hnorm : ‖Z‖ < r := by simpa [mem_ball_zero_iff] using hZ
    calc
      ‖expTermFDeriv Z n‖ ≤
          ((n : ℝ) / n.factorial) * ‖Z‖ ^ n.pred :=
        norm_expTermFDeriv_le Z n
      _ ≤ ((n : ℝ) / n.factorial) * r ^ n.pred := by
        gcongr
  have hseries := hasFDerivAt_tsum_of_isPreconnected
    (u := fun n : ℕ => ((n : ℝ) / n.factorial) * r ^ n.pred)
    (s := Metric.ball (0 : 𝔸) r)
    (f := fun n Z => ((n.factorial : ℝ)⁻¹) • Z ^ n)
    (f' := fun n Z => expTermFDeriv Z n)
    (x₀ := (0 : 𝔸)) (x := Y)
    hu Metric.isOpen_ball (convex_ball (0 : 𝔸) r).isPreconnected
    (fun n Z _ => hasFDerivAt_invFactorial_smul_pow Z n)
    hbound (Metric.mem_ball_self (by positivity))
    (NormedSpace.expSeries_summable' (𝕂 := ℝ) (0 : 𝔸))
    (by simpa [mem_ball_zero_iff] using hYr)
  rw [NormedSpace.exp_eq_tsum ℝ]
  exact hseries

/-- The Fréchet derivative itself is the ordered insertion series. -/
theorem fderiv_exp_eq_ordered [NormOneClass 𝔸] (Y : 𝔸) :
    fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸) Y =
      ∑' n : ℕ, expTermFDeriv Y n :=
  (hasFDerivAt_exp_ordered Y).fderiv

end

end YangMills.RG
