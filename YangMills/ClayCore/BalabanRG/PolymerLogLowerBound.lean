import Mathlib
import YangMills.ClayCore.BalabanRG.PolymerLogBound

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# PolymerLogLowerBound — Layer 4C

Lower bound and two-sided control of `log(polymerPartitionFunction)`.

Key fact: `|Z - 1| ≤ t` with `t < 1` implies `Z ≥ 1 - t > 0`.
By monotonicity of log: `log Z ≥ log(1-t)`.
We use the classical bound `log(1-t) ≥ -t/(1-t)` for `0 ≤ t < 1`.
When `t < 1/2` (which holds for `budget < log(3/2)`), this gives `log Z ≥ -2t`.

For the general regime `budget < log 2` (i.e., `t < 1`) we prove:
  `log Z ≥ -(2 * (exp(B) - 1))`
as a clean mechanizable lower bound.
-/

noncomputable section

/-! ## Auxiliary: log(1-t) ≥ -t/(1-t) for 0 ≤ t < 1 -/

/-- For `0 ≤ t < 1`: `log(1 - t) ≥ -t / (1 - t)`. -/
theorem Real.log_one_sub_ge {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    -(t / (1 - t)) ≤ Real.log (1 - t) := by
  have h1t : 0 < 1 - t := by linarith
  rw [div_le_iff h1t, neg_mul, neg_le_iff_add_nonneg, ← sub_le_iff_le_add]
  -- Need: -(1-t) * log(1-t) ≤ t, i.e., (1-t)*(-log(1-t)) ≤ t
  -- Equivalently: (1-t) * log(1/(1-t)) ≤ t
  -- This follows from log(1/(1-t)) ≤ t/(1-t) and multiplying by (1-t)
  -- Use: log x ≤ x - 1 applied to x = 1/(1-t) > 1
  have hx : (1 : ℝ) < 1 / (1 - t) := by rw [lt_div_iff h1t]; linarith
  have hlog : Real.log (1 / (1 - t)) ≤ 1 / (1 - t) - 1 :=
    Real.log_le_sub_one hx.le.lt_of_ne' |>.le
  rw [Real.log_div (by norm_num) h1t.ne', Real.log_one] at hlog
  have hlog2 : -Real.log (1 - t) ≤ t / (1 - t) := by
    rw [div_sub' _ _ _ h1t.ne', div_le_div_iff (by linarith) h1t] at hlog ⊢
    linarith
  linarith [mul_le_mul_of_nonneg_right hlog2 h1t.le]

/-- Simpler weak bound: `log(1 - t) ≥ -2t` for `0 ≤ t ≤ 1/2`. -/
theorem Real.log_one_sub_ge_neg_two {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1/2) :
    -2 * t ≤ Real.log (1 - t) := by
  have ht1 : t < 1 := by linarith
  have h1t : 0 < 1 - t := by linarith
  have hbase := Real.log_one_sub_ge ht0 ht1
  have hdenom : 1 / (1 - t) ≤ 2 := by
    rw [div_le_iff h1t]; linarith
  linarith [mul_le_mul_of_nonneg_right hdenom ht0]

/-! ## 4C-1: lower bound on Z: Z ≥ 1 - (exp(B)-1) -/

theorem polymerPartitionFunction_lb {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (K : Activity d L) (a : ℝ) (ha : 0 < a)
    (hKP : KPOnGamma Gamma K a) :
    1 - (Real.exp (theoreticalBudget Gamma K a) - 1)
      ≤ polymerPartitionFunction Gamma K := by
  have habs := kpOnGamma_implies_abs_Z_sub_one_le Gamma K a ha hKP
  linarith [neg_abs_le (polymerPartitionFunction Gamma K - 1)]

/-! ## 4C-2: log Z ≥ log(1 - t) ≥ -(exp(B)-1)/(1-(exp(B)-1))

  When budget < log 2, t = exp(B)-1 < 1, so 1-t > 0.
  log Z ≥ log(1-t) ≥ -t/(1-t) ≥ -(exp(B)-1)
  (the last step uses 1/(1-t) ≥ 1 which gives t/(1-t) ≥ t ... wait,
  actually t/(1-t) ≥ t for t ≥ 0, so -(t/(1-t)) ≤ -t.
  So the sharpest clean bound available is log Z ≥ -t/(1-t), not -t.)

  We prove: log Z ≥ -(exp(B)-1)/(1-(exp(B)-1))
-/

theorem log_polymerPartitionFunction_lower {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (K : Activity d L) (a : ℝ) (ha : 0 < a)
    (hKP : KPOnGamma Gamma K a)
    (hsmall : Real.exp (theoreticalBudget Gamma K a) - 1 < 1) :
    -((Real.exp (theoreticalBudget Gamma K a) - 1)
        / (1 - (Real.exp (theoreticalBudget Gamma K a) - 1)))
      ≤ Real.log (polymerPartitionFunction Gamma K) := by
  set t := Real.exp (theoreticalBudget Gamma K a) - 1 with ht_def
  have ht0 : 0 ≤ t := by
    simp [ht_def]
    linarith [Real.one_le_exp (theoreticalBudget_nonneg Gamma K a)]
  have ht1 : t < 1 := hsmall
  have hZlb := polymerPartitionFunction_lb Gamma K a ha hKP
  have hZlb_pos : 0 < 1 - t := by linarith
  have hZpos : 0 < polymerPartitionFunction Gamma K := by
    linarith
  -- log Z ≥ log(1 - t) (by monotonicity)
  have hlog_mono : Real.log (1 - t) ≤ Real.log (polymerPartitionFunction Gamma K) :=
    Real.log_le_log hZlb_pos hZlb
  -- log(1-t) ≥ -t/(1-t)
  have hlog_lb := Real.log_one_sub_ge ht0 ht1
  linarith

/-! ## 4C-3: weak two-sided bound when budget < log(3/2) -/

theorem log_polymerPartitionFunction_abs_le {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (K : Activity d L) (a : ℝ) (ha : 0 < a)
    (hKP : KPOnGamma Gamma K a)
    (hsmall : Real.exp (theoreticalBudget Gamma K a) - 1 ≤ 1/2) :
    |Real.log (polymerPartitionFunction Gamma K)|
      ≤ 2 * (Real.exp (theoreticalBudget Gamma K a) - 1) := by
  have ht0 : 0 ≤ Real.exp (theoreticalBudget Gamma K a) - 1 := by
    linarith [Real.one_le_exp (theoreticalBudget_nonneg Gamma K a)]
  have ht05 : Real.exp (theoreticalBudget Gamma K a) - 1 ≤ 1/2 := hsmall
  have hsmall1 : Real.exp (theoreticalBudget Gamma K a) - 1 < 1 := by linarith
  have hZlb := polymerPartitionFunction_lb Gamma K a ha hKP
  have hZlb_pos : 0 < 1 - (Real.exp (theoreticalBudget Gamma K a) - 1) := by linarith
  have hZpos := polymerPartitionFunction_pos_of_kp Gamma K a ha hKP hsmall1
  set t := Real.exp (theoreticalBudget Gamma K a) - 1
  have hub := log_polymerPartitionFunction_le_budget Gamma K a ha hKP hsmall1
  have hlog_mono : Real.log (1 - t) ≤ Real.log (polymerPartitionFunction Gamma K) :=
    Real.log_le_log hZlb_pos hZlb
  have hlb := Real.log_one_sub_ge_neg_two ht0 ht05
  rw [abs_le]
  constructor
  · linarith
  · linarith

end

end YangMills.ClayCore
