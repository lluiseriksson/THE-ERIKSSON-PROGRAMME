/- Copyright (c) 2026 Lluis Eriksson.
SPDX-License-Identifier: AGPL-3.0-or-later -/

import AmosClosure.BesselInterface

/-!
# The derivative of `besselI` (arc C2.2, charter Amendment 6)

Termwise differentiation of the `besselI` power series on an open
ball with dominated derivatives (Mathlib's `SmoothSeries` machinery)
yields the derivative identity `I_n' = I_{n+1} + (n/x) I_n`
(DLMF 10.29.2 rearranged by the recurrence), hence the
logarithmic-derivative identity `(log I_n)'(x) = ρ_n(x) + n/x` as a
genuine `HasDerivAt`, and the strict increase of
`deriv (log ∘ besselI)` across orders under the Amos bound — closing
the reading of the unit step as log-derivative monotonicity.
-/

open Metric

namespace AmosClosure

/-- Derivative of the `k`-th series term. -/
noncomputable def besselTermDeriv (n k : ℕ) (y : ℝ) : ℝ :=
  ((n + 2 * k : ℕ) : ℝ) * (y / 2) ^ (n + 2 * k - 1)
    / (2 * (k.factorial * (n + k).factorial))

lemma besselTerm_hasDerivAt (n k : ℕ) (y : ℝ) :
    HasDerivAt (fun z => besselTerm n k z) (besselTermDeriv n k y) y := by
  have h1 : HasDerivAt (fun z : ℝ => z / 2) (1 / 2) y :=
    (hasDerivAt_id y).div_const 2
  have h3 : HasDerivAt (fun z : ℝ => (z / 2) ^ (n + 2 * k))
      (((n + 2 * k : ℕ) : ℝ) * (y / 2) ^ (n + 2 * k - 1) * (1 / 2)) y := by
    simpa using h1.pow (n + 2 * k)
  have h4 := h3.div_const ((k.factorial * (n + k).factorial : ℕ) : ℝ)
  have hfun : (fun z => besselTerm n k z)
      = fun z => (z / 2) ^ (n + 2 * k)
        / ((k.factorial * (n + k).factorial : ℕ) : ℝ) := by
    funext z
    unfold besselTerm
    push_cast
    ring
  rw [hfun]
  convert h4 using 1
  unfold besselTermDeriv
  push_cast
  ring

/-- The dominating sequence for the derivatives on the ball
`|y| < x + 1`, built from `A = (x+2)/2 ≥ 1`. -/
noncomputable def besselDerivBound (n : ℕ) (x : ℝ) (k : ℕ) : ℝ :=
  ((2 * ((x + 2) / 2)) ^ n / (2 * n.factorial))
    * (((2 * ((x + 2) / 2)) ^ 2) ^ k / k.factorial)

lemma summable_besselDerivBound (n : ℕ) (x : ℝ) :
    Summable (besselDerivBound n x) :=
  (Real.summable_pow_div_factorial ((2 * ((x + 2) / 2)) ^ 2)).mul_left _

/-- Dominated-derivative estimate on the ball. -/
lemma besselTermDeriv_le (n k : ℕ) {x y : ℝ} (hx : 0 < x)
    (hy : y ∈ ball (0 : ℝ) (x + 1)) :
    ‖besselTermDeriv n k y‖ ≤ besselDerivBound n x k := by
  have hyx : |y| < x + 1 := by
    simpa [Real.dist_eq] using mem_ball.mp hy
  set A : ℝ := (x + 2) / 2 with hA_def
  have hA1 : (1 : ℝ) ≤ A := by rw [hA_def]; linarith
  have hA0 : (0 : ℝ) < A := by linarith
  have hyA : |y / 2| ≤ A := by
    rw [abs_div, abs_two, hA_def]
    have h : |y| ≤ x + 2 := by linarith
    linarith
  have hfk : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have hfn : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have hfnk : (0 : ℝ) < (n + k).factorial := by
    exact_mod_cast (n + k).factorial_pos
  have hle : (n.factorial : ℝ) ≤ (n + k).factorial := by
    exact_mod_cast Nat.factorial_le (Nat.le_add_right n k)
  have hbound_eq : besselDerivBound n x k
      = (2 * A) ^ (n + 2 * k) / (2 * ((n.factorial : ℝ) * k.factorial)) := by
    unfold besselDerivBound
    rw [← hA_def, pow_add, pow_mul]
    ring
  rw [hbound_eq]
  have hDbig : (0 : ℝ) < 2 * ((k.factorial : ℝ) * (n + k).factorial) :=
    mul_pos two_pos (mul_pos hfk hfnk)
  have hDsmall : (0 : ℝ) < 2 * ((n.factorial : ℝ) * k.factorial) :=
    mul_pos two_pos (mul_pos hfn hfk)
  have hden : 2 * ((n.factorial : ℝ) * k.factorial)
      ≤ 2 * ((k.factorial : ℝ) * (n + k).factorial) := by
    have h := mul_le_mul_of_nonneg_left hle hfk.le
    nlinarith [h]
  have hnum : |((n + 2 * k : ℕ) : ℝ) * (y / 2) ^ (n + 2 * k - 1)|
      ≤ (2 * A) ^ (n + 2 * k) := by
    rcases Nat.eq_zero_or_pos (n + 2 * k) with hm0 | hmpos
    · rw [hm0]
      simp
    · obtain ⟨m', hm'⟩ : ∃ m', n + 2 * k = m' + 1 :=
        ⟨n + 2 * k - 1, by omega⟩
      rw [hm']
      rw [abs_mul, abs_pow]
      have h1 : |((m' + 1 : ℕ) : ℝ)| ≤ 2 ^ (m' + 1) := by
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((m' + 1 : ℕ) : ℝ))]
        exact_mod_cast (Nat.lt_pow_self (by norm_num) (n := m' + 1)).le
      have h2 : |y / 2| ^ (m' + 1 - 1) ≤ A ^ (m' + 1) := by
        have h2a : |y / 2| ^ m' ≤ A ^ m' := by
          gcongr
        have h2b : A ^ m' ≤ A ^ m' * A :=
          le_mul_of_one_le_right (by positivity) hA1
        calc |y / 2| ^ (m' + 1 - 1) = |y / 2| ^ m' := by norm_num
          _ ≤ A ^ m' := h2a
          _ ≤ A ^ m' * A := h2b
          _ = A ^ (m' + 1) := by rw [pow_succ]
      calc |((m' + 1 : ℕ) : ℝ)| * |y / 2| ^ (m' + 1 - 1)
          ≤ 2 ^ (m' + 1) * A ^ (m' + 1) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = (2 * A) ^ (m' + 1) := by rw [mul_pow]
  unfold besselTermDeriv
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hDbig]
  rw [div_le_div_iff₀ hDbig hDsmall]
  calc |((n + 2 * k : ℕ) : ℝ) * (y / 2) ^ (n + 2 * k - 1)|
        * (2 * ((n.factorial : ℝ) * k.factorial))
      ≤ (2 * A) ^ (n + 2 * k) * (2 * ((n.factorial : ℝ) * k.factorial)) :=
        mul_le_mul_of_nonneg_right hnum hDsmall.le
    _ ≤ (2 * A) ^ (n + 2 * k)
        * (2 * ((k.factorial : ℝ) * (n + k).factorial)) :=
        mul_le_mul_of_nonneg_left hden (by positivity)

set_option maxHeartbeats 1000000 in
/-- **The derivative of `besselI`, from the series**: for `x > 0`,
`I_n'(x) = I_{n+1}(x) + (n/x)·I_n(x)`. -/
theorem besselI_hasDerivAt (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (besselI n)
      (besselI (n + 1) x + (n : ℝ) / x * besselI n x) x := by
  have hxball : x ∈ ball (0 : ℝ) (x + 1) := by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hx]
    linarith
  have hderiv : HasDerivAt (fun z => ∑' k, besselTerm n k z)
      (∑' k, besselTermDeriv n k x) x := by
    apply hasDerivAt_tsum_of_isPreconnected
      (summable_besselDerivBound n x) isOpen_ball
      (convex_ball (0 : ℝ) (x + 1)).isPreconnected
      (fun k y _ => besselTerm_hasDerivAt n k y)
      (fun k y hy => besselTermDeriv_le n k hx hy)
      hxball (summable_besselTerm n hx.le) hxball
  have hsum_eq : ∑' k, besselTermDeriv n k x
      = besselI (n + 1) x + (n : ℝ) / x * besselI n x := by
    have hx' : x ≠ 0 := ne_of_gt hx
    have hs0 := summable_besselTerm n hx.le
    have hs1 := summable_besselTerm (n + 1) hx.le
    have hsD : Summable (fun k => besselTermDeriv n k x) :=
      Summable.of_norm_bounded (summable_besselDerivBound n x)
        (fun k => besselTermDeriv_le n k hx hxball)
    -- termwise: D_0 = (n/x)·t_{n,0};  D_{k+1} = (n/x)·t_{n,k+1} + t_{n+1,k}
    have hkey0 : besselTermDeriv n 0 x = (n : ℝ) / x * besselTerm n 0 x := by
      unfold besselTermDeriv besselTerm
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · subst hn0; simp
      · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        simp only [Nat.mul_zero, Nat.add_zero, Nat.factorial_zero]
        rw [show n' + 1 - 1 = n' from rfl, pow_succ]
        push_cast
        field_simp
    have hkeyS : ∀ k, besselTermDeriv n (k + 1) x
        = (n : ℝ) / x * besselTerm n (k + 1) x + besselTerm (n + 1) k x := by
      intro k
      unfold besselTermDeriv besselTerm
      have e1 : n + 2 * (k + 1) - 1 = n + 2 * k + 1 := by omega
      have e2 : n + 2 * (k + 1) = (n + 2 * k + 1) + 1 := by omega
      have e3 : n + 1 + 2 * k = n + 2 * k + 1 := by omega
      have e4 : n + 1 + k = n + k + 1 := by omega
      rw [e1, e2, e3, e4]
      rw [show (k + 1).factorial = (k + 1) * k.factorial from
        Nat.factorial_succ k]
      have hf1 : ((k.factorial : ℝ)) ≠ 0 := by
        exact_mod_cast k.factorial_ne_zero
      have hf2 : (((n + k + 1).factorial : ℝ)) ≠ 0 := by
        exact_mod_cast (n + k + 1).factorial_ne_zero
      rw [pow_succ]
      push_cast
      field_simp
      ring_nf
    have hshiftD : Summable (fun k => besselTermDeriv n (k + 1) x) :=
      (summable_nat_add_iff 1).mpr hsD
    have hshift0 : Summable (fun k => besselTerm n (k + 1) x) :=
      (summable_nat_add_iff 1).mpr hs0
    have hshift0' : Summable
        (fun k => (n : ℝ) / x * besselTerm n (k + 1) x) :=
      hshift0.mul_left _
    calc ∑' k, besselTermDeriv n k x
        = besselTermDeriv n 0 x + ∑' k, besselTermDeriv n (k + 1) x :=
          hsD.tsum_eq_zero_add
      _ = (n : ℝ) / x * besselTerm n 0 x
          + ∑' k, ((n : ℝ) / x * besselTerm n (k + 1) x
            + besselTerm (n + 1) k x) := by
          rw [hkey0]
          congr 1
          exact tsum_congr hkeyS
      _ = (n : ℝ) / x * besselTerm n 0 x
          + ((∑' k, (n : ℝ) / x * besselTerm n (k + 1) x)
            + ∑' k, besselTerm (n + 1) k x) := by
          rw [hshift0'.tsum_add hs1]
      _ = (n : ℝ) / x * (besselTerm n 0 x + ∑' k, besselTerm n (k + 1) x)
          + besselI (n + 1) x := by
          rw [tsum_mul_left]
          unfold besselI
          ring
      _ = besselI (n + 1) x + (n : ℝ) / x * besselI n x := by
          rw [show besselI n x = ∑' k, besselTerm n k x from rfl,
            hs0.tsum_eq_zero_add]
          ring
  have hfinal : HasDerivAt (fun z => ∑' k, besselTerm n k z)
      (besselI (n + 1) x + (n : ℝ) / x * besselI n x) x := by
    rw [← hsum_eq]
    exact hderiv
  exact hfinal

/-- **The logarithmic-derivative identity, formalized**:
`(log ∘ besselI n)'(x) = ρ_n(x) + n/x` as a `HasDerivAt`. -/
theorem besselI_log_hasDerivAt (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y => Real.log (besselI n y))
      (besselI (n + 1) x / besselI n x + (n : ℝ) / x) x := by
  have hpos := besselI_pos n hx
  have h := (besselI_hasDerivAt n hx).log (ne_of_gt hpos)
  convert h using 1
  field_simp

/-- **Log-derivative monotonicity across orders, in `deriv` form**:
under the Amos bound at order `n`, the derivative of `log I_n` at `x`
is strictly below that of `log I_{n+1}` — the unit-step inequality
with the log-derivative identity now formalized, not classical. -/
theorem besselI_logDeriv_lt (n : ℕ) {x : ℝ} (hx : 0 < x)
    (hamos : AmosBound n x (besselI (n + 1) x / besselI n x)) :
    deriv (fun y => Real.log (besselI n y)) x
      < deriv (fun y => Real.log (besselI (n + 1) y)) x := by
  rw [(besselI_log_hasDerivAt n hx).deriv,
    (besselI_log_hasDerivAt (n + 1) hx).deriv]
  have h := besselI_logderiv_step n hx hamos
  push_cast
  linarith

end AmosClosure
