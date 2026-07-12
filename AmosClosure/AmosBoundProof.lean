/- Copyright (c) 2026 Lluis Eriksson.
SPDX-License-Identifier: AGPL-3.0-or-later -/

import AmosClosure.Riccati

/-!
# The Amos bound: series bounds and the zone (arc C3, phase 2a)

Product-form geometric series bounds for `besselI`, the `ψ`
function `ψ_n(x) = x·(1/ρ_n − ρ_n)`, its derivative from the
Riccati equation, and the ZONE THEOREM: `ψ_n > 2n+1` on
`0 < x ≤ 1/4`, uniformly in `n`.  (Phase 2b, the barrier, consumes
these.)
-/

namespace AmosClosure

/-! ### Series bounds (product form throughout) -/

/-- Termwise geometric domination: `t_{n,k} ≤ t_{n,0}·q^k` with
`q = (x/2)²/(n+1)`. -/
lemma besselTerm_le_geometric (n k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    besselTerm n k x
      ≤ besselTerm n 0 x * ((x / 2) ^ 2 / ((n : ℝ) + 1)) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : besselTerm n (k + 1) x
        ≤ besselTerm n k x * ((x / 2) ^ 2 / ((n : ℝ) + 1)) := by
      unfold besselTerm
      have e1 : n + 2 * (k + 1) = (n + 2 * k) + 2 := by omega
      rw [e1, pow_add]
      have hfk : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
      have hfnk : (0 : ℝ) < (n + k).factorial := by
        exact_mod_cast (n + k).factorial_pos
      have hkfac : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * k.factorial := by
        push_cast [Nat.factorial_succ]
        ring
      have hnkfac : ((n + (k + 1)).factorial : ℝ)
          = ((n : ℝ) + k + 1) * (n + k).factorial := by
        rw [show n + (k + 1) = (n + k) + 1 from by omega]
        push_cast [Nat.factorial_succ]
        ring
      rw [hkfac, hnkfac, div_mul_div_comm]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : ((n : ℝ) + 1) ≤ ((k : ℝ) + 1) * ((n : ℝ) + k + 1) := by
        nlinarith [Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) n]
      have hA : (0 : ℝ) ≤ (x / 2) ^ (n + 2 * k) * (x / 2) ^ 2 := by
        positivity
      nlinarith [mul_le_mul_of_nonneg_left h1
        (mul_nonneg hA (mul_nonneg hfk.le hfnk.le))]
    calc besselTerm n (k + 1) x
        ≤ besselTerm n k x * ((x / 2) ^ 2 / ((n : ℝ) + 1)) := hstep
      _ ≤ (besselTerm n 0 x * ((x / 2) ^ 2 / ((n : ℝ) + 1)) ^ k)
          * ((x / 2) ^ 2 / ((n : ℝ) + 1)) := by
          apply mul_le_mul_of_nonneg_right ih (by positivity)
      _ = besselTerm n 0 x * ((x / 2) ^ 2 / ((n : ℝ) + 1)) ^ (k + 1) := by
          rw [pow_succ]; ring

/-- Geometric upper bound in product form:
`(1−q)·I_n(x) ≤ t_{n,0}` when `q = (x/2)²/(n+1) < 1`. -/
lemma besselI_mul_le (n : ℕ) {x : ℝ} (hx : 0 < x)
    (hq : (x / 2) ^ 2 / ((n : ℝ) + 1) < 1) :
    (1 - (x / 2) ^ 2 / ((n : ℝ) + 1)) * besselI n x
      ≤ besselTerm n 0 x := by
  have hq0 : (0 : ℝ) ≤ (x / 2) ^ 2 / ((n : ℝ) + 1) := by positivity
  have hgeo : Summable
      (fun k => besselTerm n 0 x * ((x / 2) ^ 2 / ((n : ℝ) + 1)) ^ k) :=
    (summable_geometric_of_lt_one hq0 hq).mul_left _
  have hle := (summable_besselTerm n hx.le).tsum_le_tsum
    (fun k => besselTerm_le_geometric n k hx.le) hgeo
  have hsum : ∑' k, besselTerm n 0 x * ((x / 2) ^ 2 / ((n : ℝ) + 1)) ^ k
      = besselTerm n 0 x * (1 - (x / 2) ^ 2 / ((n : ℝ) + 1))⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq]
  have h1q : (0 : ℝ) < 1 - (x / 2) ^ 2 / ((n : ℝ) + 1) := by linarith
  have hI : besselI n x
      ≤ besselTerm n 0 x * (1 - (x / 2) ^ 2 / ((n : ℝ) + 1))⁻¹ := by
    calc besselI n x
        ≤ ∑' k, besselTerm n 0 x * ((x / 2) ^ 2 / ((n : ℝ) + 1)) ^ k := hle
      _ = _ := hsum
  have h1q' : (1 - (x / 2) ^ 2 / ((n : ℝ) + 1)) ≠ 0 := ne_of_gt h1q
  calc (1 - (x / 2) ^ 2 / ((n : ℝ) + 1)) * besselI n x
      ≤ (1 - (x / 2) ^ 2 / ((n : ℝ) + 1))
        * (besselTerm n 0 x * (1 - (x / 2) ^ 2 / ((n : ℝ) + 1))⁻¹) :=
        mul_le_mul_of_nonneg_left hI h1q.le
    _ = besselTerm n 0 x := by
        rw [mul_comm (besselTerm n 0 x) _, ← mul_assoc,
          mul_inv_cancel₀ h1q', one_mul]

/-- Strict first-term lower bound: `t_{n,0} < I_n(x)` for `x > 0`. -/
lemma besselTerm_zero_lt_besselI (n : ℕ) {x : ℝ} (hx : 0 < x) :
    besselTerm n 0 x < besselI n x := by
  have hsum := summable_besselTerm n hx.le
  have h2 : ∑ k ∈ Finset.range 2, besselTerm n k x ≤ besselI n x :=
    hsum.sum_le_tsum _ (fun j _ => besselTerm_nonneg n j hx.le)
  have hpos1 : 0 < besselTerm n 1 x := besselTerm_pos n 1 hx
  have hexp : ∑ k ∈ Finset.range 2, besselTerm n k x
      = besselTerm n 0 x + besselTerm n 1 x := by
    simp [Finset.sum_range_succ]
  linarith [h2]

/-- Exact first-term ratio identity: `2(n+1)·t_{n+1,0} = x·t_{n,0}`. -/
lemma besselTerm_zero_succ (n : ℕ) (x : ℝ) :
    2 * ((n : ℝ) + 1) * besselTerm (n + 1) 0 x = x * besselTerm n 0 x := by
  unfold besselTerm
  simp only [Nat.mul_zero, Nat.add_zero, Nat.factorial_zero]
  have hfac : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * n.factorial := by
    push_cast [Nat.factorial_succ]
    ring
  rw [hfac, pow_succ]
  have hfn : ((n.factorial : ℝ)) ≠ 0 := by
    exact_mod_cast n.factorial_ne_zero
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-! ### The ψ function -/

/-- Abbreviation for the ratio. -/
noncomputable def besselRatio (n : ℕ) (x : ℝ) : ℝ :=
  besselI (n + 1) x / besselI n x

lemma besselRatio_pos (n : ℕ) {x : ℝ} (hx : 0 < x) :
    0 < besselRatio n x :=
  div_pos (besselI_pos (n + 1) hx) (besselI_pos n hx)

/-- `ψ_n(x) = x·(1/ρ_n(x) − ρ_n(x))`. -/
noncomputable def besselPsi (n : ℕ) (x : ℝ) : ℝ :=
  x * (1 / besselRatio n x - besselRatio n x)

/-- Derivative of `ψ` from the Riccati equation. -/
lemma besselPsi_hasDerivAt (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (besselPsi n)
      ((1 / besselRatio n x - besselRatio n x)
        + x * (-(riccatiQ n x (besselRatio n x)) / besselRatio n x ^ 2
          - riccatiQ n x (besselRatio n x))) x := by
  have hρ := besselRatio_pos n hx
  have hρ' : besselRatio n x ≠ 0 := ne_of_gt hρ
  have hR : HasDerivAt (besselRatio n)
      (riccatiQ n x (besselRatio n x)) x := besselRatio_hasDerivAt n hx
  have hinv : HasDerivAt (fun y => 1 / besselRatio n y)
      (-(riccatiQ n x (besselRatio n x)) / besselRatio n x ^ 2) x := by
    simpa [one_div] using hR.inv hρ'
  have hsub : HasDerivAt
      (fun y => 1 / besselRatio n y - besselRatio n y)
      (-(riccatiQ n x (besselRatio n x)) / besselRatio n x ^ 2
        - riccatiQ n x (besselRatio n x)) x := hinv.sub hR
  have hprod := (hasDerivAt_id x).mul hsub
  have hfn2 : (id * fun y => 1 / besselRatio n y - besselRatio n y)
      = fun y : ℝ => y * (1 / besselRatio n y - besselRatio n y) := by
    funext y
    simp [Pi.mul_apply]
  rw [hfn2] at hprod
  simp only [id_eq] at hprod
  have hfun : besselPsi n = fun y =>
      y * (1 / besselRatio n y - besselRatio n y) := rfl
  have hval : (1 / besselRatio n x - besselRatio n x)
      + x * (-(riccatiQ n x (besselRatio n x)) / besselRatio n x ^ 2
        - riccatiQ n x (besselRatio n x))
      = 1 * (1 / besselRatio n x - besselRatio n x)
        + x * (-riccatiQ n x (besselRatio n x) / besselRatio n x ^ 2
          - riccatiQ n x (besselRatio n x)) := by ring
  rw [hfun, hval]
  exact hprod

/-! ### The zone theorem -/

/-- **ZONE**: `ψ_n(x) > 2n+1` for `0 < x ≤ 1/4`, uniformly in `n`. -/
theorem besselPsi_zone (n : ℕ) {x : ℝ} (hx : 0 < x) (hx4 : x ≤ 1 / 4) :
    (2 * (n : ℝ) + 1) < besselPsi n x := by
  have hI0 := besselI_pos n hx
  have hI1 := besselI_pos (n + 1) hx
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hx2 : x ^ 2 ≤ 1 / 16 := by nlinarith
  -- q at order n+1, with its exact cast shape
  have hcast : (((n + 1 : ℕ) : ℝ) + 1) = (n : ℝ) + 2 := by push_cast; ring
  have hq0 : (0 : ℝ) ≤ (x / 2) ^ 2 / (((n + 1 : ℕ) : ℝ) + 1) := by
    positivity
  have hqmul : ((x / 2) ^ 2 / (((n + 1 : ℕ) : ℝ) + 1)) * ((n : ℝ) + 2)
      = (x / 2) ^ 2 := by
    rw [hcast]
    field_simp
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by linarith
  have hq2 : 2 * ((n : ℝ) + 1) * ((x / 2) ^ 2 / (((n + 1 : ℕ) : ℝ) + 1))
      ≤ x ^ 2 / 2 := by
    nlinarith [hqmul, hq0, sq_nonneg x]
  have hqhalf : (x / 2) ^ 2 / (((n + 1 : ℕ) : ℝ) + 1) ≤ 1 / 2 := by
    nlinarith [hqmul, hq0]
  have hq1 : (x / 2) ^ 2 / (((n + 1 : ℕ) : ℝ) + 1) < 1 := by linarith
  -- product-form facts
  have hup : (1 - (x / 2) ^ 2 / (((n + 1 : ℕ) : ℝ) + 1))
      * besselI (n + 1) x ≤ besselTerm (n + 1) 0 x :=
    besselI_mul_le (n + 1) hx hq1
  have hlo : besselTerm n 0 x < besselI n x :=
    besselTerm_zero_lt_besselI n hx
  have hid : 2 * ((n : ℝ) + 1) * besselTerm (n + 1) 0 x
      = x * besselTerm n 0 x := besselTerm_zero_succ n x
  have ht0pos : 0 < besselTerm n 0 x := besselTerm_pos n 0 hx
  -- coefficient inequality: 2n+1+x² ≤ 2(n+1)(1−q)
  have hcoef : 2 * (n : ℝ) + 1 + x ^ 2
      ≤ 2 * ((n : ℝ) + 1)
        * (1 - (x / 2) ^ 2 / (((n + 1 : ℕ) : ℝ) + 1)) := by
    nlinarith [hq2, hx2]
  -- key strict chain: (2n+1+x²)·I_{n+1} < x·I_n
  have hkey : (2 * (n : ℝ) + 1 + x ^ 2) * besselI (n + 1) x
      < x * besselI n x := by
    have s1 : (2 * (n : ℝ) + 1 + x ^ 2) * besselI (n + 1) x
        ≤ (2 * ((n : ℝ) + 1)
            * (1 - (x / 2) ^ 2 / (((n + 1 : ℕ) : ℝ) + 1)))
          * besselI (n + 1) x :=
      mul_le_mul_of_nonneg_right hcoef hI1.le
    have s2 : (2 * ((n : ℝ) + 1)
          * (1 - (x / 2) ^ 2 / (((n + 1 : ℕ) : ℝ) + 1)))
        * besselI (n + 1) x
        ≤ 2 * ((n : ℝ) + 1) * besselTerm (n + 1) 0 x := by
      have := mul_le_mul_of_nonneg_left hup
        (by positivity : (0 : ℝ) ≤ 2 * ((n : ℝ) + 1))
      calc (2 * ((n : ℝ) + 1)
            * (1 - (x / 2) ^ 2 / (((n + 1 : ℕ) : ℝ) + 1)))
          * besselI (n + 1) x
          = 2 * ((n : ℝ) + 1)
            * ((1 - (x / 2) ^ 2 / (((n + 1 : ℕ) : ℝ) + 1))
              * besselI (n + 1) x) := by ring
        _ ≤ 2 * ((n : ℝ) + 1) * besselTerm (n + 1) 0 x := this
    have s4 : x * besselTerm n 0 x < x * besselI n x :=
      mul_lt_mul_of_pos_left hlo hx
    linarith [s1, s2, hid, s4]
  -- convert to ψ via multiplication by I_{n+1}·I_n > 0
  have hABpos : 0 < besselI (n + 1) x * besselI n x := mul_pos hI1 hI0
  have hψmul : besselPsi n x * (besselI (n + 1) x * besselI n x)
      = x * (besselI n x * besselI n x
        - besselI (n + 1) x * besselI (n + 1) x) := by
    unfold besselPsi besselRatio
    field_simp
  have hfin : (2 * (n : ℝ) + 1) * (besselI (n + 1) x * besselI n x)
      < x * (besselI n x * besselI n x
        - besselI (n + 1) x * besselI (n + 1) x) := by
    have h1 : besselI n x * ((2 * (n : ℝ) + 1 + x ^ 2) * besselI (n + 1) x)
        < besselI n x * (x * besselI n x) :=
      mul_lt_mul_of_pos_left hkey hI0
    have h2 : besselI (n + 1) x ≤ x * besselI n x := by
      have hc1 : (1 : ℝ) ≤ 2 * (n : ℝ) + 1 + x ^ 2 := by
        nlinarith [sq_nonneg x]
      nlinarith [hkey, hI1.le]
    have h3 : (0 : ℝ) ≤ x * besselI (n + 1) x
        * (x * besselI n x - besselI (n + 1) x) := by
      apply mul_nonneg (mul_nonneg hx.le hI1.le)
      linarith [h2]
    nlinarith [h1, h3]
  have hlt : (2 * (n : ℝ) + 1) * (besselI (n + 1) x * besselI n x)
      < besselPsi n x * (besselI (n + 1) x * besselI n x) := by
    rw [hψmul]
    exact hfin
  exact lt_of_mul_lt_mul_right hlt hABpos.le

end AmosClosure
