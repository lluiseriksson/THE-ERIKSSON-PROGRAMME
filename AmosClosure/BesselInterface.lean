/- Copyright (c) 2026 Lluis Eriksson.
SPDX-License-Identifier: AGPL-3.0-or-later -/

import AmosClosure.Core

/-!
# The Bessel interface (arc C2.1, charter Amendment 3)

Integer-order modified Bessel functions of the first kind, defined by
their power series, with convergence, positivity, and the three-term
recurrence DLMF 10.29.1 proved as THEOREMS in the pinned core.  The
consumer theorems of `AmosClosure.Core` are then restated over the
TRUE `besselI`: the recurrence hypotheses are discharged, and
`AmosBound` — now about genuine Bessel ratios — remains the sole
named analytic hypothesis.
-/

namespace AmosClosure

/-- `k`-th term of the power series of `I_n(x)`:
`(x/2)^(n+2k) / (k! (n+k)!)`. -/
noncomputable def besselTerm (n k : ℕ) (x : ℝ) : ℝ :=
  (x / 2) ^ (n + 2 * k) / (k.factorial * (n + k).factorial)

/-- Integer-order modified Bessel function of the first kind, as the
sum of its power series. -/
noncomputable def besselI (n : ℕ) (x : ℝ) : ℝ := ∑' k, besselTerm n k x

lemma besselTerm_nonneg (n k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ besselTerm n k x := by
  unfold besselTerm
  positivity

lemma besselTerm_pos (n k : ℕ) {x : ℝ} (hx : 0 < x) :
    0 < besselTerm n k x := by
  unfold besselTerm
  positivity

/-- Exponential-series majorant: `t_{n,k}(x) ≤ ((x/2)^n/n!) · ((x/2)²)^k/k!`. -/
lemma besselTerm_le (n k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    besselTerm n k x ≤
      ((x / 2) ^ n / n.factorial) * (((x / 2) ^ 2) ^ k / k.factorial) := by
  unfold besselTerm
  rw [pow_add, pow_mul, div_mul_div_comm]
  have hA : (0 : ℝ) ≤ (x / 2) ^ n * ((x / 2) ^ 2) ^ k := by positivity
  have hfk : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have hfn : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have hfnk : (0 : ℝ) < (n + k).factorial := by
    exact_mod_cast (n + k).factorial_pos
  have hle : (n.factorial : ℝ) ≤ (n + k).factorial := by
    exact_mod_cast Nat.factorial_le (Nat.le_add_right n k)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc (x / 2) ^ n * ((x / 2) ^ 2) ^ k * ((n.factorial : ℝ) * k.factorial)
      = ((x / 2) ^ n * ((x / 2) ^ 2) ^ k * k.factorial) * n.factorial := by
        ring
    _ ≤ ((x / 2) ^ n * ((x / 2) ^ 2) ^ k * k.factorial) * (n + k).factorial := by
        apply mul_le_mul_of_nonneg_left hle (by positivity)
    _ = (x / 2) ^ n * ((x / 2) ^ 2) ^ k * ((k.factorial : ℝ) * (n + k).factorial) := by
        ring

lemma summable_besselTerm (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun k => besselTerm n k x) := by
  refine Summable.of_nonneg_of_le
    (fun k => besselTerm_nonneg n k hx)
    (fun k => besselTerm_le n k hx) ?_
  exact (Real.summable_pow_div_factorial ((x / 2) ^ 2)).mul_left _

/-- Positivity of `I_n(x)` for `x > 0`. -/
theorem besselI_pos (n : ℕ) {x : ℝ} (hx : 0 < x) : 0 < besselI n x := by
  have hsum := summable_besselTerm n hx.le
  have h0 : besselTerm n 0 x ≤ besselI n x := by
    apply hsum.le_tsum 0
    intro j _
    exact besselTerm_nonneg n j hx.le
  exact lt_of_lt_of_le (besselTerm_pos n 0 hx) h0

/-- The `k = 0` case of the termwise recurrence identity. -/
lemma besselTerm_rec_zero (n : ℕ) {x : ℝ} (hx : x ≠ 0) :
    2 * ((n : ℝ) + 1) / x * besselTerm (n + 1) 0 x = besselTerm n 0 x := by
  unfold besselTerm
  simp only [Nat.mul_zero, Nat.add_zero, Nat.factorial_zero]
  rw [show (n + 1).factorial = (n + 1) * n.factorial from Nat.factorial_succ n]
  have hx2 : x / 2 ≠ 0 := by
    simp [div_eq_zero_iff]
    exact hx
  rw [pow_succ]
  push_cast
  field_simp

/-- The successor case of the termwise recurrence identity:
`(2(n+1)/x)·t_{n+1,k+1} = t_{n,k+1} − t_{n+2,k}`. -/
lemma besselTerm_rec_succ (n k : ℕ) {x : ℝ} (hx : x ≠ 0) :
    2 * ((n : ℝ) + 1) / x * besselTerm (n + 1) (k + 1) x
      = besselTerm n (k + 1) x - besselTerm (n + 2) k x := by
  unfold besselTerm
  have e1 : n + 1 + 2 * (k + 1) = (n + 2 * (k + 1)) + 1 := by omega
  have e2 : n + 2 + 2 * k = n + 2 * (k + 1) := by omega
  have e3 : n + 1 + (k + 1) = n + k + 2 := by omega
  have e4 : n + (k + 1) = n + k + 1 := by omega
  have e5 : n + 2 + k = n + k + 2 := by omega
  rw [e1, e2, e3, e4, e5]
  rw [show (k + 1).factorial = (k + 1) * k.factorial from Nat.factorial_succ k]
  rw [show (n + k + 2).factorial = (n + k + 2) * (n + k + 1).factorial from
    Nat.factorial_succ (n + k + 1)]
  have hf1 : ((k.factorial : ℝ)) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hf2 : (((n + k + 1).factorial : ℝ)) ≠ 0 := by
    exact_mod_cast (n + k + 1).factorial_ne_zero
  rw [pow_succ]
  push_cast
  field_simp
  ring

/-- **The three-term recurrence, DLMF 10.29.1, as a theorem** (at
order `n+1`, in the shape the consumers take):
`I_n(x) − I_{n+2}(x) = (2(n+1)/x)·I_{n+1}(x)`. -/
theorem besselI_recurrence (n : ℕ) {x : ℝ} (hx : 0 < x) :
    besselI n x - besselI (n + 2) x
      = 2 * ((n : ℝ) + 1) / x * besselI (n + 1) x := by
  have hs0 := summable_besselTerm n hx.le
  have hs1 := summable_besselTerm (n + 1) hx.le
  have hs2 := summable_besselTerm (n + 2) hx.le
  have hs1' : Summable (fun k => 2 * ((n : ℝ) + 1) / x * besselTerm (n + 1) k x) :=
    hs1.mul_left _
  -- expand the RHS series at index 0 and reindex
  have hshift : Summable (fun k => 2 * ((n : ℝ) + 1) / x * besselTerm (n + 1) (k + 1) x) :=
    (summable_nat_add_iff 1).mpr hs1'
  have hsn_shift : Summable (fun k => besselTerm n (k + 1) x) :=
    (summable_nat_add_iff 1).mpr hs0
  have hrhs : 2 * ((n : ℝ) + 1) / x * besselI (n + 1) x
      = besselTerm n 0 x
        + ∑' k, (besselTerm n (k + 1) x - besselTerm (n + 2) k x) := by
    rw [besselI, ← tsum_mul_left, hs1'.tsum_eq_zero_add]
    rw [besselTerm_rec_zero n (ne_of_gt hx)]
    congr 1
    exact tsum_congr fun k => besselTerm_rec_succ n k (ne_of_gt hx)
  have hsplit : ∑' k, (besselTerm n (k + 1) x - besselTerm (n + 2) k x)
      = (∑' k, besselTerm n (k + 1) x) - ∑' k, besselTerm (n + 2) k x :=
    Summable.tsum_sub hsn_shift hs2
  have hleft : besselI n x = besselTerm n 0 x + ∑' k, besselTerm n (k + 1) x := by
    rw [besselI, hs0.tsum_eq_zero_add]
  rw [hrhs, hsplit, hleft, besselI]
  ring

/-- Ratio form of the recurrence, as consumed by the φ-track:
`1/ρ_n = ρ_{n+1} + 2(n+1)/x` with `ρ_n = I_{n+1}/I_n`. -/
theorem besselI_ratio_recurrence (n : ℕ) {x : ℝ} (hx : 0 < x) :
    1 / (besselI (n + 1) x / besselI n x)
      = besselI (n + 2) x / besselI (n + 1) x + 2 * ((n : ℝ) + 1) / x := by
  have h0 := besselI_pos n hx
  have h1 := besselI_pos (n + 1) hx
  have hrec := besselI_recurrence n hx
  rw [one_div_div]
  have : besselI n x / besselI (n + 1) x - besselI (n + 2) x / besselI (n + 1) x
      = 2 * ((n : ℝ) + 1) / x := by
    rw [div_sub_div_same, hrec, mul_div_cancel_right₀ _ (ne_of_gt h1)]
  linarith [this]

/-- **Unit step for true Bessel values.**  The recurrence hypothesis of
`unit_step_of_recurrence_and_amos` is discharged by
`besselI_recurrence`; `AmosBound` over the true ratio is the sole
remaining hypothesis. -/
theorem besselI_unit_step (n : ℕ) {x : ℝ} (hx : 0 < x)
    (hamos : AmosBound n x (besselI (n + 1) x / besselI n x)) :
    besselI (n + 1) x / besselI n x
      - besselI (n + 2) x / besselI (n + 1) x < 1 / x := by
  have h := unit_step_of_recurrence_and_amos x n
    (besselI n x) (besselI (n + 1) x) (besselI (n + 2) x)
    hx (Nat.cast_nonneg n) (besselI_pos n hx) (besselI_pos (n + 1) hx)
    (by rw [besselI_recurrence n hx])
    hamos
  exact h

/-- **Log-derivative unit step for true Bessel values.** -/
theorem besselI_logderiv_step (n : ℕ) {x : ℝ} (hx : 0 < x)
    (hamos : AmosBound n x (besselI (n + 1) x / besselI n x)) :
    0 < (besselI (n + 2) x / besselI (n + 1) x + ((n : ℝ) + 1) / x)
      - (besselI (n + 1) x / besselI n x + (n : ℝ) / x) :=
  logderiv_unit_step_increase x n
    (besselI n x) (besselI (n + 1) x) (besselI (n + 2) x)
    hx (Nat.cast_nonneg n) (besselI_pos n hx) (besselI_pos (n + 1) hx)
    (by rw [besselI_recurrence n hx])
    hamos

/-- **The φ-monotonicity step for true Bessel ratios.**  Both
recurrence hypotheses of `phi_step_of_recurrences` are discharged by
`besselI_recurrence`; `AmosBound` at the middle order is the sole
remaining hypothesis.  Stated at orders `(m, m+1, m+2)` with the real
φ-parameter `m+1 ≥ 1`. -/
theorem besselI_phi_step (m : ℕ) {x : ℝ} (hx : 0 < x)
    (hAmos : AmosBound ((m : ℝ) + 1) x
      (besselI (m + 2) x / besselI (m + 1) x)) :
    (((m : ℝ) + 1 - 1) / (besselI (m + 1) x / besselI m x) ^ 2
        + ((m : ℝ) + 1 + 1) * (besselI (m + 2) x / besselI (m + 1) x) ^ 2)
      / ((m : ℝ) + 1)
    < (((m : ℝ) + 1) / (besselI (m + 2) x / besselI (m + 1) x) ^ 2
        + ((m : ℝ) + 1 + 2) * (besselI (m + 3) x / besselI (m + 2) x) ^ 2)
      / ((m : ℝ) + 1 + 1) := by
  have h0 := besselI_pos m hx
  have h1 := besselI_pos (m + 1) hx
  have h2 := besselI_pos (m + 2) hx
  have hrec1 : 1 / (besselI (m + 1) x / besselI m x)
      = besselI (m + 2) x / besselI (m + 1) x + 2 * ((m : ℝ) + 1) / x := by
    exact besselI_ratio_recurrence m hx
  have hrec2 : besselI (m + 3) x / besselI (m + 2) x
      = 1 / (besselI (m + 2) x / besselI (m + 1) x)
        - 2 * (((m : ℝ) + 1) + 1) / x := by
    have h := besselI_ratio_recurrence (m + 1) hx
    rw [show m + 1 + 1 = m + 2 from rfl, show m + 1 + 2 = m + 3 from rfl] at h
    push_cast at h ⊢
    linarith [h]
  exact phi_step_of_recurrences ((m : ℝ) + 1) x
    (besselI (m + 1) x / besselI m x)
    (besselI (m + 2) x / besselI (m + 1) x)
    (besselI (m + 3) x / besselI (m + 2) x)
    (by linarith [Nat.cast_nonneg (α := ℝ) m]) hx
    (div_pos h1 h0) (div_pos h2 h1)
    (by linarith [hrec1])
    (by linarith [hrec2])
    hAmos

end AmosClosure
