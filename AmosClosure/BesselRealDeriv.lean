/- Copyright (c) 2026 Lluis Eriksson.
SPDX-License-Identifier: AGPL-3.0-or-later -/

import AmosClosure.BesselRealInterface

/-!
# The derivative of `besselIReal` (arc C4, phase 2; charter Amendment 2)

Termwise differentiation of the Γ-power series on the open interval
`(x/2, 3x/2) ⊂ (0,∞)` — the `rpow` domain forbids the C2.2 ball
through `0` — with the REGISTERED dominated-derivative design:
`k = 0` treated separately (its exponent `ν−1` is negative for
`ν < 1`, so the supremum sits at the LEFT endpoint; at `ν = 0` the
term is exactly zero), and for `k ≥ 1` the factoring
`ν+2k−1 = (ν+1) + 2(k−1)` which never reintroduces a negative
exponent.  Yields `I_ν'(x) = I_{ν+1}(x) + (ν/x)·I_ν(x)` as a
`HasDerivAt`, the `deriv`-form identity, the log-derivative
identity, and the ν = n consistency value test through the
identification theorem.
-/

open Set

namespace AmosClosure

/-- Derivative of the `k`-th Γ-series term at real order. -/
noncomputable def besselRealTermDeriv (ν : ℝ) (k : ℕ) (y : ℝ) : ℝ :=
  (ν + 2 * k) * (y / 2) ^ (ν + 2 * (k : ℝ) - 1)
    / (2 * (k.factorial * Real.Gamma (ν + k + 1)))

/-- `rpow` split of the even part of an exponent (phase-1 pattern,
factored): `b^(c + 2k) = b^c · (b²)^k` for `b > 0`. -/
lemma rpow_add_two_mul {b : ℝ} (hb : 0 < b) (c : ℝ) (k : ℕ) :
    b ^ (c + 2 * (k : ℝ)) = b ^ c * (b ^ 2) ^ k := by
  rw [Real.rpow_add hb]
  congr 1
  have h2k : (2 : ℝ) * (k : ℝ) = ((2 * k : ℕ) : ℝ) := by push_cast; ring
  rw [h2k, Real.rpow_natCast, pow_mul]

lemma besselRealTerm_hasDerivAt (ν : ℝ) (k : ℕ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun z => besselRealTerm ν k z)
      (besselRealTermDeriv ν k y) y := by
  have hy2 : y / 2 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun z : ℝ => z / 2) (1 / 2) y :=
    (hasDerivAt_id y).div_const 2
  have h3 := h1.rpow_const (p := ν + 2 * (k : ℝ)) (Or.inl hy2)
  have h4 := h3.div_const ((k.factorial : ℝ) * Real.Gamma (ν + k + 1))
  have hfun : (fun z => besselRealTerm ν k z)
      = fun z => (z / 2) ^ (ν + 2 * (k : ℝ))
        / ((k.factorial : ℝ) * Real.Gamma (ν + k + 1)) := rfl
  rw [hfun]
  convert h4 using 1
  unfold besselRealTermDeriv
  ring

/-- The dominating sequence on `(x/2, 3x/2)`, per the REGISTERED
design: separate `k = 0` value (left-endpoint-safe via the sum of
both endpoint powers), and for `k ≥ 1` the `(ν+1)+2(k−1)` factoring
with `A = (3x/4)²`. -/
noncomputable def besselRealDerivBound (ν x : ℝ) : ℕ → ℝ
  | 0 => ν * ((x / 4) ^ (ν - 1) + (3 * x / 4) ^ (ν - 1))
      / (2 * Real.Gamma (ν + 1))
  | (k + 1) => (ν + 2 * ((k : ℝ) + 1)) * (3 * x / 4) ^ (ν + 1)
      * ((3 * x / 4) ^ 2) ^ k
      / (2 * ((k + 1).factorial * Real.Gamma (ν + 1)))

/-- `k = 0` dominated-derivative estimate (REGISTERED subcase): the
uniform bound `(y/2)^(ν−1) ≤ (x/4)^(ν−1) + (3x/4)^(ν−1)` covers both
monotonicity regimes; at `ν = 0` both sides carry the factor `ν = 0`. -/
lemma besselRealTerm_deriv_zero_bound (ν : ℝ) (hν : 0 ≤ ν) {x y : ℝ}
    (hx : 0 < x) (hy : y ∈ Ioo (x / 2) (3 * x / 2)) :
    ‖besselRealTermDeriv ν 0 y‖ ≤ besselRealDerivBound ν x 0 := by
  obtain ⟨hy1, hy2⟩ := hy
  have hy0 : 0 < y := by linarith
  have hyl : x / 4 ≤ y / 2 := by linarith
  have hyr : y / 2 ≤ 3 * x / 4 := by linarith
  have hgpos : 0 < Real.Gamma (ν + 1) :=
    Real.Gamma_pos_of_pos (by linarith)
  simp only [besselRealTermDeriv, besselRealDerivBound, Nat.cast_zero,
    mul_zero, add_zero, Nat.factorial_zero, Nat.cast_one, one_mul]
  have hkey : (y / 2) ^ (ν - 1) ≤ (x / 4) ^ (ν - 1) + (3 * x / 4) ^ (ν - 1) := by
    rcases le_total 1 ν with h1 | h1
    · calc (y / 2) ^ (ν - 1) ≤ (3 * x / 4) ^ (ν - 1) :=
            Real.rpow_le_rpow (by positivity) hyr (by linarith)
        _ ≤ (x / 4) ^ (ν - 1) + (3 * x / 4) ^ (ν - 1) :=
            le_add_of_nonneg_left (Real.rpow_nonneg (by positivity) _)
    · calc (y / 2) ^ (ν - 1) ≤ (x / 4) ^ (ν - 1) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hyl (by linarith)
        _ ≤ (x / 4) ^ (ν - 1) + (3 * x / 4) ^ (ν - 1) :=
            le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _)
  have hnonneg : (0 : ℝ) ≤ ν * (y / 2) ^ (ν - 1) / (2 * Real.Gamma (ν + 1)) := by
    apply div_nonneg _ (by positivity)
    exact mul_nonneg hν (Real.rpow_nonneg (by positivity) _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hnum : ν * (y / 2) ^ (ν - 1)
      ≤ ν * ((x / 4) ^ (ν - 1) + (3 * x / 4) ^ (ν - 1)) :=
    mul_le_mul_of_nonneg_left hkey hν
  have hden : (0 : ℝ) ≤ 2 * Real.Gamma (ν + 1) := by positivity
  nlinarith [hnum, hden, mul_le_mul_of_nonneg_right hnum hden]

/-- `k+1` dominated-derivative estimate (REGISTERED factoring
`ν+2(k+1)−1 = (ν+1)+2k`): both `rpow` exponents stay `≥ 1`, no
negative exponent ever appears. -/
lemma besselRealTerm_deriv_succ_bound (ν : ℝ) (hν : 0 ≤ ν) (k : ℕ)
    {x y : ℝ} (hx : 0 < x) (hy : y ∈ Ioo (x / 2) (3 * x / 2)) :
    ‖besselRealTermDeriv ν (k + 1) y‖ ≤ besselRealDerivBound ν x (k + 1) := by
  obtain ⟨hy1, hy2⟩ := hy
  have hy0 : 0 < y := by linarith
  have hy20 : (0 : ℝ) < y / 2 := by linarith
  have hyr : y / 2 ≤ 3 * x / 4 := by linarith
  have harg : (0 : ℝ) < ν + (k + 1 : ℕ) + 1 := by
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    push_cast
    linarith
  have hgbig : 0 < Real.Gamma (ν + (k + 1 : ℕ) + 1) :=
    Real.Gamma_pos_of_pos harg
  have hg1 : 0 < Real.Gamma (ν + 1) :=
    Real.Gamma_pos_of_pos (by linarith)
  have hgle : Real.Gamma (ν + 1) ≤ Real.Gamma (ν + (k + 1 : ℕ) + 1) :=
    gamma_le_gamma_add ν hν (k + 1)
  have hfpos : (0 : ℝ) < (k + 1).factorial := by
    exact_mod_cast (k + 1).factorial_pos
  -- exponent factoring: ν + 2(k+1) − 1 = (ν+1) + 2k
  have hexp : ν + 2 * ((k + 1 : ℕ) : ℝ) - 1 = (ν + 1) + 2 * (k : ℝ) := by
    push_cast; ring
  have hsplit : (y / 2) ^ (ν + 2 * ((k + 1 : ℕ) : ℝ) - 1)
      = (y / 2) ^ (ν + 1) * ((y / 2) ^ 2) ^ k := by
    rw [hexp, rpow_add_two_mul hy20]
  have hcoef : (0 : ℝ) ≤ ν + 2 * ((k + 1 : ℕ) : ℝ) := by
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    push_cast
    linarith
  have hb1 : (y / 2) ^ (ν + 1) ≤ (3 * x / 4) ^ (ν + 1) :=
    Real.rpow_le_rpow hy20.le hyr (by linarith)
  have hb2 : ((y / 2) ^ 2) ^ k ≤ ((3 * x / 4) ^ 2) ^ k := by
    have hbase : (y / 2) ^ 2 ≤ (3 * x / 4) ^ 2 := by nlinarith [hy20, hyr]
    exact pow_le_pow_left₀ (by positivity) hbase k
  have hDpos : (0 : ℝ) < 2 * (((k + 1).factorial : ℝ)
      * Real.Gamma (ν + (k + 1 : ℕ) + 1)) := by positivity
  have hDsmall : (0 : ℝ) < 2 * (((k + 1).factorial : ℝ)
      * Real.Gamma (ν + 1)) := by positivity
  have hnonneg : (0 : ℝ) ≤ (ν + 2 * ((k + 1 : ℕ) : ℝ))
      * (y / 2) ^ (ν + 2 * ((k + 1 : ℕ) : ℝ) - 1)
      / (2 * (((k + 1).factorial : ℝ) * Real.Gamma (ν + (k + 1 : ℕ) + 1))) := by
    apply div_nonneg _ hDpos.le
    exact mul_nonneg hcoef (Real.rpow_nonneg hy20.le _)
  unfold besselRealTermDeriv
  simp only [besselRealDerivBound]
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, hsplit]
  have hnum : (ν + 2 * ((k + 1 : ℕ) : ℝ)) * ((y / 2) ^ (ν + 1) * ((y / 2) ^ 2) ^ k)
      ≤ (ν + 2 * ((k : ℝ) + 1)) * (3 * x / 4) ^ (ν + 1) * ((3 * x / 4) ^ 2) ^ k := by
    have hc : (ν + 2 * ((k + 1 : ℕ) : ℝ)) = ν + 2 * ((k : ℝ) + 1) := by
      push_cast; ring
    rw [hc]
    have h1 : (y / 2) ^ (ν + 1) * ((y / 2) ^ 2) ^ k
        ≤ (3 * x / 4) ^ (ν + 1) * ((3 * x / 4) ^ 2) ^ k := by
      apply mul_le_mul hb1 hb2 (by positivity)
        (Real.rpow_nonneg (by positivity) _)
    calc (ν + 2 * ((k : ℝ) + 1)) * ((y / 2) ^ (ν + 1) * ((y / 2) ^ 2) ^ k)
        ≤ (ν + 2 * ((k : ℝ) + 1))
            * ((3 * x / 4) ^ (ν + 1) * ((3 * x / 4) ^ 2) ^ k) := by
          apply mul_le_mul_of_nonneg_left h1
          push_cast at hcoef ⊢
          linarith
      _ = (ν + 2 * ((k : ℝ) + 1)) * (3 * x / 4) ^ (ν + 1)
            * ((3 * x / 4) ^ 2) ^ k := by ring
  have hden : 2 * (((k + 1).factorial : ℝ) * Real.Gamma (ν + 1))
      ≤ 2 * (((k + 1).factorial : ℝ) * Real.Gamma (ν + (k + 1 : ℕ) + 1)) := by
    have := mul_le_mul_of_nonneg_left hgle hfpos.le
    linarith
  rw [div_le_div_iff₀ hDpos hDsmall]
  calc (ν + 2 * ((k + 1 : ℕ) : ℝ)) * ((y / 2) ^ (ν + 1) * ((y / 2) ^ 2) ^ k)
        * (2 * (((k + 1).factorial : ℝ) * Real.Gamma (ν + 1)))
      ≤ ((ν + 2 * ((k : ℝ) + 1)) * (3 * x / 4) ^ (ν + 1) * ((3 * x / 4) ^ 2) ^ k)
        * (2 * (((k + 1).factorial : ℝ) * Real.Gamma (ν + 1))) :=
        mul_le_mul_of_nonneg_right hnum hDsmall.le
    _ ≤ ((ν + 2 * ((k : ℝ) + 1)) * (3 * x / 4) ^ (ν + 1) * ((3 * x / 4) ^ 2) ^ k)
        * (2 * (((k + 1).factorial : ℝ) * Real.Gamma (ν + (k + 1 : ℕ) + 1))) := by
        apply mul_le_mul_of_nonneg_left hden
        have h0 : (0 : ℝ) ≤ (ν + 2 * ((k : ℝ) + 1)) := by
          have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
          linarith
        apply mul_nonneg (mul_nonneg h0 (Real.rpow_nonneg (by positivity) _))
        positivity

/-- Summability of the registered majorant: the tail is dominated by
`(ν+2)·C·A^k/k!` since `(ν+2k+2)/(k+1)! ≤ (ν+2)/k!` (equivalent to
`0 ≤ νk`). -/
lemma summable_besselRealDerivMajorant (ν : ℝ) (hν : 0 ≤ ν) {x : ℝ}
    (hx : 0 < x) : Summable (besselRealDerivBound ν x) := by
  apply (summable_nat_add_iff 1).mp
  have hg1 : 0 < Real.Gamma (ν + 1) :=
    Real.Gamma_pos_of_pos (by linarith)
  set B : ℝ := (3 * x / 4) ^ (ν + 1) with hB_def
  set A : ℝ := (3 * x / 4) ^ 2 with hA_def
  have hB0 : 0 ≤ B := Real.rpow_nonneg (by positivity) _
  have hA0 : 0 ≤ A := by positivity
  refine Summable.of_nonneg_of_le ?_ ?_
    (((Real.summable_pow_div_factorial A).mul_left
      ((ν + 2) * B / (2 * Real.Gamma (ν + 1)))))
  · intro k
    simp only [besselRealDerivBound]
    apply div_nonneg _ (by positivity)
    apply mul_nonneg (mul_nonneg _ hB0) (pow_nonneg hA0 k)
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  · intro k
    simp only [besselRealDerivBound]
    have hfact : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * k.factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hfk : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hEq : (ν + 2 * ((k : ℝ) + 1)) * B * A ^ k
          / (2 * (((k + 1).factorial : ℝ) * Real.Gamma (ν + 1)))
        = ((ν + 2 * ((k : ℝ) + 1)) / ((k : ℝ) + 1))
          * (B * A ^ k / (2 * ((k.factorial : ℝ) * Real.Gamma (ν + 1)))) := by
      rw [hfact]
      have h1 : ((k : ℝ) + 1) ≠ 0 := by positivity
      have h2 : (k.factorial : ℝ) ≠ 0 := ne_of_gt hfk
      have h3 : Real.Gamma (ν + 1) ≠ 0 := ne_of_gt hg1
      field_simp
    rw [hEq]
    have hq : (ν + 2 * ((k : ℝ) + 1)) / ((k : ℝ) + 1) ≤ ν + 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg hν hk]
    have hr : (0 : ℝ) ≤ B * A ^ k / (2 * ((k.factorial : ℝ) * Real.Gamma (ν + 1))) := by
      apply div_nonneg (mul_nonneg hB0 (pow_nonneg hA0 k)) (by positivity)
    calc ((ν + 2 * ((k : ℝ) + 1)) / ((k : ℝ) + 1))
          * (B * A ^ k / (2 * ((k.factorial : ℝ) * Real.Gamma (ν + 1))))
        ≤ (ν + 2) * (B * A ^ k / (2 * ((k.factorial : ℝ) * Real.Gamma (ν + 1)))) :=
          mul_le_mul_of_nonneg_right hq hr
      _ = (ν + 2) * B / (2 * Real.Gamma (ν + 1)) * (A ^ k / k.factorial) := by
          field_simp

set_option maxHeartbeats 1000000 in
/-- **The derivative of `besselIReal`, from the series** (arc C4
phase 2): for `ν ≥ 0`, `x > 0`,
`I_ν'(x) = I_{ν+1}(x) + (ν/x)·I_ν(x)`. -/
theorem besselIReal_hasDerivAt (ν : ℝ) (hν : 0 ≤ ν) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y => besselIReal ν y)
      (besselIReal (ν + 1) x + ν / x * besselIReal ν x) x := by
  have hxmem : x ∈ Ioo (x / 2) (3 * x / 2) := ⟨by linarith, by linarith⟩
  have hx2 : (0 : ℝ) < x / 2 := by linarith
  have hboundAt : ∀ (k : ℕ) (y : ℝ), y ∈ Ioo (x / 2) (3 * x / 2) →
      ‖besselRealTermDeriv ν k y‖ ≤ besselRealDerivBound ν x k := by
    intro k y hy
    match k with
    | 0 => exact besselRealTerm_deriv_zero_bound ν hν hx hy
    | (k + 1) => exact besselRealTerm_deriv_succ_bound ν hν k hx hy
  have hderiv : HasDerivAt (fun z => ∑' k, besselRealTerm ν k z)
      (∑' k, besselRealTermDeriv ν k x) x := by
    apply hasDerivAt_tsum_of_isPreconnected
      (summable_besselRealDerivMajorant ν hν hx) isOpen_Ioo
      (convex_Ioo (x / 2) (3 * x / 2)).isPreconnected
      (fun k y hy => besselRealTerm_hasDerivAt ν k (by
        have := hy.1; linarith))
      hboundAt hxmem (summable_besselRealTerm ν hν hx) hxmem
  have hsum_eq : ∑' k, besselRealTermDeriv ν k x
      = besselIReal (ν + 1) x + ν / x * besselIReal ν x := by
    have hx' : x ≠ 0 := ne_of_gt hx
    have hs0 := summable_besselRealTerm ν hν hx
    have hs1 := summable_besselRealTerm (ν + 1) (by linarith) hx
    have hsD : Summable (fun k => besselRealTermDeriv ν k x) :=
      Summable.of_norm_bounded (summable_besselRealDerivMajorant ν hν hx)
        (fun k => hboundAt k x hxmem)
    have hgamma_ne : Real.Gamma (ν + 1) ≠ 0 :=
      ne_of_gt (Real.Gamma_pos_of_pos (by linarith))
    -- termwise: D_0 = (ν/x)·t_{ν,0};  D_{k+1} = (ν/x)·t_{ν,k+1} + t_{ν+1,k}
    have hkey0 : besselRealTermDeriv ν 0 x = ν / x * besselRealTerm ν 0 x := by
      unfold besselRealTermDeriv besselRealTerm
      simp only [Nat.cast_zero, mul_zero, add_zero, Nat.factorial_zero,
        Nat.cast_one, one_mul]
      have hsplit : (x / 2) ^ ν = (x / 2) ^ (ν - 1) * (x / 2) := by
        have h := Real.rpow_add hx2 (ν - 1) 1
        rw [Real.rpow_one, show ν - 1 + 1 = ν by ring] at h
        exact h
      rw [hsplit]
      field_simp
    have hkeyS : ∀ k, besselRealTermDeriv ν (k + 1) x
        = ν / x * besselRealTerm ν (k + 1) x + besselRealTerm (ν + 1) k x := by
      intro k
      unfold besselRealTermDeriv besselRealTerm
      have harg2 : (0 : ℝ) < ν + k + 2 := by
        have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith
      have hgamma_ne2 : Real.Gamma (ν + k + 2) ≠ 0 :=
        ne_of_gt (Real.Gamma_pos_of_pos harg2)
      -- unify the three Γ arguments to Γ(ν+k+2)
      have hg1 : Real.Gamma (ν + (k + 1 : ℕ) + 1) = Real.Gamma (ν + k + 2) := by
        rw [show ν + ((k + 1 : ℕ) : ℝ) + 1 = ν + k + 2 by push_cast; ring]
      have hg2 : Real.Gamma ((ν + 1) + k + 1) = Real.Gamma (ν + k + 2) := by
        rw [show (ν + 1) + (k : ℝ) + 1 = ν + k + 2 by ring]
      -- unify exponents around E = ν + 2k + 1
      have he1 : ν + 2 * ((k + 1 : ℕ) : ℝ) - 1 = ν + 2 * (k : ℝ) + 1 := by
        push_cast; ring
      have he3 : (ν + 1) + 2 * (k : ℝ) = ν + 2 * (k : ℝ) + 1 := by ring
      have hsplit : (x / 2) ^ (ν + 2 * ((k + 1 : ℕ) : ℝ))
          = (x / 2) ^ (ν + 2 * (k : ℝ) + 1) * (x / 2) := by
        have h := Real.rpow_add hx2 (ν + 2 * (k : ℝ) + 1) 1
        rw [Real.rpow_one,
          show ν + 2 * (k : ℝ) + 1 + 1 = ν + 2 * ((k + 1 : ℕ) : ℝ) by
            push_cast; ring] at h
        exact h
      have hfact : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * k.factorial := by
        rw [Nat.factorial_succ]; push_cast; ring
      rw [he1, hg1, he3, hg2, hsplit, hfact]
      have hf : (k.factorial : ℝ) ≠ 0 := by
        exact_mod_cast k.factorial_ne_zero
      have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      push_cast
      ring
    have hshift0 : Summable (fun k => besselRealTerm ν (k + 1) x) :=
      (summable_nat_add_iff 1).mpr hs0
    have hshift0' : Summable
        (fun k => ν / x * besselRealTerm ν (k + 1) x) :=
      hshift0.mul_left _
    calc ∑' k, besselRealTermDeriv ν k x
        = besselRealTermDeriv ν 0 x + ∑' k, besselRealTermDeriv ν (k + 1) x :=
          hsD.tsum_eq_zero_add
      _ = ν / x * besselRealTerm ν 0 x
          + ∑' k, (ν / x * besselRealTerm ν (k + 1) x
            + besselRealTerm (ν + 1) k x) := by
          rw [hkey0]
          congr 1
          exact tsum_congr hkeyS
      _ = ν / x * besselRealTerm ν 0 x
          + ((∑' k, ν / x * besselRealTerm ν (k + 1) x)
            + ∑' k, besselRealTerm (ν + 1) k x) := by
          rw [hshift0'.tsum_add hs1]
      _ = ν / x * (besselRealTerm ν 0 x + ∑' k, besselRealTerm ν (k + 1) x)
          + besselIReal (ν + 1) x := by
          rw [tsum_mul_left]
          unfold besselIReal
          ring
      _ = besselIReal (ν + 1) x + ν / x * besselIReal ν x := by
          rw [show besselIReal ν x = ∑' k, besselRealTerm ν k x from rfl,
            hs0.tsum_eq_zero_add]
          ring
  rw [← hsum_eq]
  exact hderiv

/-- The `deriv`-form of the identity (REGISTERED sequence endpoint):
`deriv I_ν (x) = I_{ν+1}(x) + (ν/x)·I_ν(x)`. -/
theorem besselIReal_deriv_identity (ν : ℝ) (hν : 0 ≤ ν) {x : ℝ}
    (hx : 0 < x) :
    deriv (fun y => besselIReal ν y) x
      = besselIReal (ν + 1) x + ν / x * besselIReal ν x :=
  (besselIReal_hasDerivAt ν hν hx).deriv

/-- Logarithmic-derivative identity at real order:
`(log I_ν)'(x) = ρ_ν(x) + ν/x` as a `HasDerivAt`. -/
theorem besselIReal_log_hasDerivAt (ν : ℝ) (hν : 0 ≤ ν) {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt (fun y => Real.log (besselIReal ν y))
      (besselIReal (ν + 1) x / besselIReal ν x + ν / x) x := by
  have hpos := besselIReal_pos ν hν hx
  have h := (besselIReal_hasDerivAt ν hν hx).log (ne_of_gt hpos)
  convert h using 1
  field_simp

/-- Internal consistency test registered in charter Amendment 2 (NOT
a judge): at `ν = n` the real-order derivative VALUE agrees with the
integer layer, through the identification theorem. -/
theorem besselIReal_deriv_value_natCast (n : ℕ) {x : ℝ} (hx : 0 < x) :
    besselIReal ((n : ℝ) + 1) x + (n : ℝ) / x * besselIReal (n : ℝ) x
      = besselI (n + 1) x + (n : ℝ) / x * besselI n x := by
  rw [show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring,
    besselIReal_natCast (n + 1) hx, besselIReal_natCast n hx]

end AmosClosure
