/- Copyright (c) 2026 Lluis Eriksson.
SPDX-License-Identifier: AGPL-3.0-or-later -/

import AmosClosure.BesselInterface

/-!
# The real-order Bessel interface (arc C4, phase 1; charter docs/C4-CHARTER.md)

Real-order modified Bessel functions `I_ν`, `ν ≥ 0`, defined by the
Gamma power series with a real exponent (`rpow`), in the pinned core:
convergence, positivity, the exact term-ratio identity, the
three-term recurrence at real order, and THE IDENTIFICATION THEOREM
`besselIReal (n : ℝ) x = besselI n x` tying the real-order object to
the integer-order development of C2/C3 by theorem, not by prose.
Everything lives at `x > 0` (the `rpow` domain of this development).
-/

namespace AmosClosure

/-- `k`-th term of the Γ-power series of `I_ν(x)`:
`(x/2)^(ν+2k) / (k! · Γ(ν+k+1))`, real exponent via `rpow`. -/
noncomputable def besselRealTerm (ν : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  (x / 2) ^ (ν + 2 * (k : ℝ)) / (k.factorial * Real.Gamma (ν + k + 1))

/-- Real-order modified Bessel function of the first kind, as the sum
of its Γ-power series. -/
noncomputable def besselIReal (ν x : ℝ) : ℝ := ∑' k, besselRealTerm ν k x

lemma gamma_arg_pos (ν : ℝ) (hν : 0 ≤ ν) (k : ℕ) : 0 < ν + k + 1 := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

lemma besselRealTerm_pos (ν : ℝ) (hν : 0 ≤ ν) (k : ℕ) {x : ℝ}
    (hx : 0 < x) : 0 < besselRealTerm ν k x := by
  unfold besselRealTerm
  apply div_pos
  · exact Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < x / 2) _
  · exact mul_pos (by exact_mod_cast k.factorial_pos)
      (Real.Gamma_pos_of_pos (gamma_arg_pos ν hν k))

lemma besselRealTerm_nonneg (ν : ℝ) (hν : 0 ≤ ν) (k : ℕ) {x : ℝ}
    (hx : 0 < x) : 0 ≤ besselRealTerm ν k x :=
  (besselRealTerm_pos ν hν k hx).le

/-- Γ does not shrink below its `k = 0` value along the series
denominators: `Γ(ν+1) ≤ Γ(ν+k+1)` for `ν ≥ 0` (each functional-equation
factor `ν+j ≥ 1`). -/
lemma gamma_le_gamma_add (ν : ℝ) (hν : 0 ≤ ν) (k : ℕ) :
    Real.Gamma (ν + 1) ≤ Real.Gamma (ν + k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have harg := gamma_arg_pos ν hν k
    have hcast : ν + (k + 1 : ℕ) + 1 = (ν + k + 1) + 1 := by
      push_cast; ring
    rw [hcast, Real.Gamma_add_one (ne_of_gt harg)]
    have hpos := Real.Gamma_pos_of_pos harg
    have hone : 1 ≤ ν + k + 1 := by
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    calc Real.Gamma (ν + 1) ≤ Real.Gamma (ν + k + 1) := ih
      _ = 1 * Real.Gamma (ν + k + 1) := by ring
      _ ≤ (ν + k + 1) * Real.Gamma (ν + k + 1) :=
          mul_le_mul_of_nonneg_right hone hpos.le

/-- Exponential-series majorant at real order:
`t_{ν,k}(x) ≤ ((x/2)^ν/Γ(ν+1)) · ((x/2)²)^k/k!`. -/
lemma besselRealTerm_le (ν : ℝ) (hν : 0 ≤ ν) (k : ℕ) {x : ℝ}
    (hx : 0 < x) :
    besselRealTerm ν k x ≤
      ((x / 2) ^ ν / Real.Gamma (ν + 1))
        * (((x / 2) ^ 2) ^ k / k.factorial) := by
  have hx2 : (0 : ℝ) < x / 2 := by linarith
  have hsplit : (x / 2) ^ (ν + 2 * (k : ℝ))
      = (x / 2) ^ ν * ((x / 2) ^ 2) ^ k := by
    rw [Real.rpow_add hx2]
    congr 1
    have h2k : (2 : ℝ) * (k : ℝ) = ((2 * k : ℕ) : ℝ) := by push_cast; ring
    rw [h2k, Real.rpow_natCast, pow_mul]
  unfold besselRealTerm
  rw [hsplit, div_mul_div_comm]
  have hA : (0 : ℝ) ≤ (x / 2) ^ ν * ((x / 2) ^ 2) ^ k := by
    have := Real.rpow_pos_of_pos hx2 ν
    positivity
  have hfk : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have hg1 : (0 : ℝ) < Real.Gamma (ν + 1) :=
    Real.Gamma_pos_of_pos (by linarith)
  have hgk : (0 : ℝ) < Real.Gamma (ν + k + 1) :=
    Real.Gamma_pos_of_pos (gamma_arg_pos ν hν k)
  have hle := gamma_le_gamma_add ν hν k
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc (x / 2) ^ ν * ((x / 2) ^ 2) ^ k * (Real.Gamma (ν + 1) * k.factorial)
      = ((x / 2) ^ ν * ((x / 2) ^ 2) ^ k * k.factorial)
          * Real.Gamma (ν + 1) := by ring
    _ ≤ ((x / 2) ^ ν * ((x / 2) ^ 2) ^ k * k.factorial)
          * Real.Gamma (ν + k + 1) := by
        apply mul_le_mul_of_nonneg_left hle (by positivity)
    _ = (x / 2) ^ ν * ((x / 2) ^ 2) ^ k
          * ((k.factorial : ℝ) * Real.Gamma (ν + k + 1)) := by ring

lemma summable_besselRealTerm (ν : ℝ) (hν : 0 ≤ ν) {x : ℝ}
    (hx : 0 < x) : Summable (fun k => besselRealTerm ν k x) := by
  refine Summable.of_nonneg_of_le
    (fun k => besselRealTerm_nonneg ν hν k hx)
    (fun k => besselRealTerm_le ν hν k hx) ?_
  exact (Real.summable_pow_div_factorial ((x / 2) ^ 2)).mul_left _

/-- Positivity of `I_ν(x)` for `ν ≥ 0`, `x > 0`. -/
theorem besselIReal_pos (ν : ℝ) (hν : 0 ≤ ν) {x : ℝ} (hx : 0 < x) :
    0 < besselIReal ν x := by
  have hsum := summable_besselRealTerm ν hν hx
  have h0 : besselRealTerm ν 0 x ≤ besselIReal ν x := by
    apply hsum.le_tsum 0
    intro j _
    exact besselRealTerm_nonneg ν hν j hx
  exact lt_of_lt_of_le (besselRealTerm_pos ν hν 0 hx) h0

/-- Exact term-ratio identity at real order:
`t_{ν,k+1} = t_{ν,k} · (x/2)² / ((k+1)(ν+k+1))`. -/
lemma besselRealTerm_succ (ν : ℝ) (hν : 0 ≤ ν) (k : ℕ) {x : ℝ}
    (hx : 0 < x) :
    besselRealTerm ν (k + 1) x
      = besselRealTerm ν k x
          * ((x / 2) ^ 2 / (((k : ℝ) + 1) * (ν + k + 1))) := by
  have hx2 : (0 : ℝ) < x / 2 := by linarith
  have harg := gamma_arg_pos ν hν k
  unfold besselRealTerm
  have he : ν + 2 * ((k + 1 : ℕ) : ℝ) = (ν + 2 * (k : ℝ)) + 2 := by
    push_cast; ring
  have hsplit : (x / 2) ^ (ν + 2 * ((k + 1 : ℕ) : ℝ))
      = (x / 2) ^ (ν + 2 * (k : ℝ)) * (x / 2) ^ 2 := by
    rw [he, Real.rpow_add hx2]
    congr 1
    have h2 : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
    rw [h2, Real.rpow_natCast]
  have hgamma : Real.Gamma (ν + (k + 1 : ℕ) + 1)
      = (ν + k + 1) * Real.Gamma (ν + k + 1) := by
    have hcast : ν + (k + 1 : ℕ) + 1 = (ν + k + 1) + 1 := by
      push_cast; ring
    rw [hcast, Real.Gamma_add_one (ne_of_gt harg)]
  have hfact : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * k.factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [hsplit, hgamma, hfact]
  have hf : (k.factorial : ℝ) ≠ 0 := by
    exact_mod_cast k.factorial_ne_zero
  have hg : Real.Gamma (ν + k + 1) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos harg)
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have ha : (ν + k + 1) ≠ 0 := ne_of_gt harg
  field_simp

/-- The `k = 0` case of the termwise recurrence identity at real
order: `(2(ν+1)/x)·t_{ν+1,0} = t_{ν,0}`. -/
lemma besselRealTerm_rec_zero (ν : ℝ) (hν : 0 ≤ ν) {x : ℝ}
    (hx : 0 < x) :
    2 * (ν + 1) / x * besselRealTerm (ν + 1) 0 x
      = besselRealTerm ν 0 x := by
  have hx2 : (0 : ℝ) < x / 2 := by linarith
  unfold besselRealTerm
  simp only [Nat.cast_zero, Nat.factorial_zero, Nat.cast_one, mul_zero,
    add_zero]
  -- post-simp goal:
  -- 2(ν+1)/x · ((x/2)^(ν+1) / (1·Γ(ν+1+1))) = (x/2)^ν / (1·Γ(ν+1))
  rw [Real.Gamma_add_one (ne_of_gt (by linarith : (0 : ℝ) < ν + 1)),
    Real.rpow_add hx2 ν 1, Real.rpow_one]
  have hg : Real.Gamma (ν + 1) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by linarith))
  have hnu1 : (ν + 1) ≠ 0 := by positivity
  have hxne : x ≠ 0 := ne_of_gt hx
  field_simp

/-- The successor case of the termwise recurrence identity at real
order: `(2(ν+1)/x)·t_{ν+1,k+1} = t_{ν,k+1} − t_{ν+2,k}`. -/
lemma besselRealTerm_rec_succ (ν : ℝ) (hν : 0 ≤ ν) (k : ℕ) {x : ℝ}
    (hx : 0 < x) :
    2 * (ν + 1) / x * besselRealTerm (ν + 1) (k + 1) x
      = besselRealTerm ν (k + 1) x - besselRealTerm (ν + 2) k x := by
  have hx2 : (0 : ℝ) < x / 2 := by linarith
  have harg1 := gamma_arg_pos ν hν (k + 1)          -- 0 < ν+(k+1)+1
  have harg2 : (0 : ℝ) < ν + k + 2 := by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  unfold besselRealTerm
  -- exponents: LHS (ν+1)+2(k+1) = E+1 with E = ν+2(k+1) = (ν+2)+2k
  have heL : (ν + 1) + 2 * ((k + 1 : ℕ) : ℝ)
      = (ν + 2 * ((k + 1 : ℕ) : ℝ)) + 1 := by push_cast; ring
  have heR : (ν + 2) + 2 * ((k : ℕ) : ℝ)
      = ν + 2 * ((k + 1 : ℕ) : ℝ) := by push_cast; ring
  have hsplitL : (x / 2) ^ ((ν + 1) + 2 * ((k + 1 : ℕ) : ℝ))
      = (x / 2) ^ (ν + 2 * ((k + 1 : ℕ) : ℝ)) * (x / 2) := by
    rw [heL, Real.rpow_add hx2, Real.rpow_one]
  -- Γ arguments: (ν+1)+(k+1)+1 = (ν+k+2)+1 ; (ν+2)+k+1 = (ν+k+2)+1 ;
  --              ν+(k+1)+1 = ν+k+2
  have hgL : Real.Gamma ((ν + 1) + (k + 1 : ℕ) + 1)
      = (ν + k + 2) * Real.Gamma (ν + k + 2) := by
    rw [show (ν + 1) + ((k + 1 : ℕ) : ℝ) + 1 = (ν + k + 2) + 1 by
      push_cast; ring]
    exact Real.Gamma_add_one (ne_of_gt harg2)
  have hgR2 : Real.Gamma ((ν + 2) + (k : ℕ) + 1)
      = (ν + k + 2) * Real.Gamma (ν + k + 2) := by
    rw [show (ν + 2) + ((k : ℕ) : ℝ) + 1 = (ν + k + 2) + 1 by ring]
    exact Real.Gamma_add_one (ne_of_gt harg2)
  have hgR1 : Real.Gamma (ν + (k + 1 : ℕ) + 1) = Real.Gamma (ν + k + 2) := by
    rw [show ν + ((k + 1 : ℕ) : ℝ) + 1 = ν + k + 2 by push_cast; ring]
  have hfact : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * k.factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [hsplitL, heR, hgL, hgR2, hgR1, hfact]
  have hf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hg : Real.Gamma (ν + k + 2) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos harg2)
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have ha2 : (ν + k + 2) ≠ 0 := ne_of_gt harg2
  field_simp
  ring

/-- **The three-term recurrence at real order** (DLMF 10.29.1 shape):
`I_ν(x) − I_{ν+2}(x) = (2(ν+1)/x)·I_{ν+1}(x)`. -/
theorem besselIReal_recurrence (ν : ℝ) (hν : 0 ≤ ν) {x : ℝ}
    (hx : 0 < x) :
    besselIReal ν x - besselIReal (ν + 2) x
      = 2 * (ν + 1) / x * besselIReal (ν + 1) x := by
  have hs0 := summable_besselRealTerm ν hν hx
  have hs1 := summable_besselRealTerm (ν + 1) (by linarith) hx
  have hs2 := summable_besselRealTerm (ν + 2) (by linarith) hx
  have hs1' : Summable (fun k => 2 * (ν + 1) / x * besselRealTerm (ν + 1) k x) :=
    hs1.mul_left _
  have hsn_shift : Summable (fun k => besselRealTerm ν (k + 1) x) :=
    (summable_nat_add_iff 1).mpr hs0
  have hrhs : 2 * (ν + 1) / x * besselIReal (ν + 1) x
      = besselRealTerm ν 0 x
        + ∑' k, (besselRealTerm ν (k + 1) x - besselRealTerm (ν + 2) k x) := by
    rw [besselIReal, ← tsum_mul_left, hs1'.tsum_eq_zero_add]
    rw [besselRealTerm_rec_zero ν hν hx]
    congr 1
    exact tsum_congr fun k => besselRealTerm_rec_succ ν hν k hx
  have hsplit : ∑' k, (besselRealTerm ν (k + 1) x - besselRealTerm (ν + 2) k x)
      = (∑' k, besselRealTerm ν (k + 1) x)
        - ∑' k, besselRealTerm (ν + 2) k x :=
    Summable.tsum_sub hsn_shift hs2
  have hleft : besselIReal ν x
      = besselRealTerm ν 0 x + ∑' k, besselRealTerm ν (k + 1) x := by
    rw [besselIReal, hs0.tsum_eq_zero_add]
  rw [hrhs, hsplit, hleft, besselIReal]
  ring

/-- **THE IDENTIFICATION THEOREM** (arc C4, the second half of C3's
declared scope limit, killed by theorem): at integer order the
Γ-series object IS the factorial-series object of the C2/C3
development.  Termwise: `rpow` collapses to the natural power and
`Γ(n+k+1) = (n+k)!`. -/
theorem besselIReal_natCast (n : ℕ) {x : ℝ} (hx : 0 < x) :
    besselIReal (n : ℝ) x = besselI n x := by
  have hx2 : (0 : ℝ) < x / 2 := by linarith
  unfold besselIReal besselI
  apply tsum_congr
  intro k
  unfold besselRealTerm besselTerm
  have hexp : ((n : ℝ) + 2 * (k : ℝ)) = ((n + 2 * k : ℕ) : ℝ) := by
    push_cast; ring
  have hpow : (x / 2) ^ ((n : ℝ) + 2 * (k : ℝ)) = (x / 2) ^ (n + 2 * k) := by
    rw [hexp, Real.rpow_natCast]
  have hgamma : Real.Gamma ((n : ℝ) + k + 1) = ((n + k).factorial : ℝ) := by
    rw [show (n : ℝ) + (k : ℝ) + 1 = ((n + k : ℕ) : ℝ) + 1 by push_cast; ring]
    exact_mod_cast Real.Gamma_nat_eq_factorial (n + k)
  rw [hpow, hgamma]

/-- Non-vacuity anchors registered in the charter: the identification
at the first two integer orders. -/
example {x : ℝ} (hx : 0 < x) : besselIReal 0 x = besselI 0 x := by
  simpa using besselIReal_natCast 0 hx

example {x : ℝ} (hx : 0 < x) : besselIReal 1 x = besselI 1 x := by
  simpa using besselIReal_natCast 1 hx

end AmosClosure
