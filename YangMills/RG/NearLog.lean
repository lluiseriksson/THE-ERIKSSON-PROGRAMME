/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib

/-!
# The near-identity logarithm (gauge-RG campaign, matrix-`log` layer brick M-log-1)

`docs/BALABAN-RG-PLAN.md` B3-full (analytic).  Bałaban's averaging
operator `Ū` (CMP 109 (0.12)) is built from the **logarithm of group
elements near the identity**, `Ū(c) = exp[ … Σ log(…) … ]·U(c)`.
Mathlib provides `NormedSpace.exp` for Banach algebras but **no
near-identity logarithm**, so this file builds it from the defining
power series

  `log(1 + Y) = Σ_{n ≥ 1} (-1)^{n+1}/n · Y^n`     (‖Y‖ < 1).

This brick establishes the **definition and convergence** of that
series in any complete normed `ℝ`-algebra (matrices over `ℝ`/`ℂ`, hence
the Lie algebra of `SU(N)`, are such).  The companion identity
`log(exp X) = X` near `0` and the Baker–Campbell–Hausdorff norm
estimates are the subsequent bricks of this layer.

**Source.** Standard analytic construction; the application is
T. Bałaban, CMP 109 (1987) (0.8),(0.12).  Strategy/framing: Lluis
Eriksson (ai.viXra:2602.0088).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no
axioms.
-/

namespace YangMills.RG

open scoped BigOperators

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- The Mercator coefficient `(-1)^{n+1}/n` of the logarithm series
(`0` at `n = 0`, so the series starts at `n = 1`). -/
noncomputable def logCoeff (n : ℕ) : ℝ :=
  if n = 0 then 0 else (-1) ^ (n + 1) / n

@[simp] theorem logCoeff_zero : logCoeff 0 = 0 := rfl

/-- For `n ≥ 1` the Mercator coefficient has absolute value `1/n ≤ 1`. -/
theorem abs_logCoeff_le_one (n : ℕ) : |logCoeff n| ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · have hn : (n : ℝ) ≠ 0 := by exact_mod_cast h.ne'
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h
    simp only [logCoeff, if_neg h.ne']
    rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast]
    rw [div_le_one (by positivity)]
    exact hn1

/-- The near-identity logarithm `log(1 + Y) = Σ_{n≥1} (-1)^{n+1}/n · Y^n`
(`NormedSpace.exp`'s local inverse), defined as the sum of the Mercator
series. -/
noncomputable def nearLog (Y : 𝔸) : 𝔸 := ∑' n : ℕ, logCoeff n • Y ^ n

/-- **Termwise geometric bound**: `‖(-1)^{n+1}/n · Y^n‖ ≤ ‖Y‖^n`
(`|coeff| ≤ 1` and `‖Y^n‖ ≤ ‖Y‖^n`). -/
theorem norm_logCoeff_smul_pow_le (Y : 𝔸) (n : ℕ) :
    ‖logCoeff n • Y ^ n‖ ≤ ‖Y‖ ^ n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · rw [norm_smul, Real.norm_eq_abs]
    calc |logCoeff n| * ‖Y ^ n‖
        ≤ 1 * ‖Y‖ ^ n :=
          mul_le_mul (abs_logCoeff_le_one n) (norm_pow_le' Y h)
            (norm_nonneg _) zero_le_one
      _ = ‖Y‖ ^ n := one_mul _

/-- **Convergence of the logarithm series** (brick M-log-1): for `‖Y‖ < 1`
the Mercator series converges absolutely in the complete normed algebra,
by termwise comparison with the geometric series. -/
theorem summable_logCoeff_smul_pow {Y : 𝔸} (hY : ‖Y‖ < 1) :
    Summable (fun n : ℕ => logCoeff n • Y ^ n) :=
  Summable.of_norm_bounded (g := fun n : ℕ => ‖Y‖ ^ n)
    (summable_geometric_of_lt_one (norm_nonneg Y) hY)
    (norm_logCoeff_smul_pow_le Y)

/-- **Quantitative bound on the near-identity logarithm** (brick M-log-1):
for `‖Y‖ < 1`, `‖log(1 + Y)‖ ≤ (1 - ‖Y‖)⁻¹` — the geometric majorant
the Baker–Campbell–Hausdorff estimates of CMP 109/122 consume. -/
theorem norm_nearLog_le {Y : 𝔸} (hY : ‖Y‖ < 1) :
    ‖nearLog Y‖ ≤ (1 - ‖Y‖)⁻¹ := by
  have hgeo : Summable (fun n : ℕ => ‖Y‖ ^ n) :=
    summable_geometric_of_lt_one (norm_nonneg Y) hY
  have hsum_norm : Summable (fun n : ℕ => ‖logCoeff n • Y ^ n‖) :=
    hgeo.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_logCoeff_smul_pow_le Y)
  calc ‖nearLog Y‖
      ≤ ∑' n : ℕ, ‖logCoeff n • Y ^ n‖ := norm_tsum_le_tsum_norm hsum_norm
    _ ≤ ∑' n : ℕ, ‖Y‖ ^ n :=
        hsum_norm.tsum_le_tsum (norm_logCoeff_smul_pow_le Y) hgeo
    _ = (1 - ‖Y‖)⁻¹ := tsum_geometric_of_lt_one (norm_nonneg Y) hY

/-- **First-order linearisation of the near-identity logarithm**
(brick M-log-2a): `nearLog Y = Y + O(‖Y‖²)`, quantitatively
`‖nearLog Y - Y‖ ≤ ‖Y‖²/(1-‖Y‖)`.  This is exactly the `O(‖·‖²)`
remainder content of Bałaban's linearisation axiom (0.8) of CMP 109
(the tie of the averaging `M` to the linear operator `Q = linAvg`),
obtained directly from the `n ≥ 2` tail of the Mercator series — it does
**not** yet require the local-inverse identity `log(exp X) = X`. -/
theorem norm_nearLog_sub_self_le {Y : 𝔸} (hY : ‖Y‖ < 1) :
    ‖nearLog Y - Y‖ ≤ ‖Y‖ ^ 2 / (1 - ‖Y‖) := by
  have hF : Summable (fun n : ℕ => logCoeff n • Y ^ n) :=
    summable_logCoeff_smul_pow hY
  have hF1 : Summable (fun n : ℕ => logCoeff (n + 1) • Y ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr hF
  have e1 : logCoeff (0 + 1) • Y ^ (0 + 1) = Y := by
    norm_num [logCoeff]
  have hsplit : nearLog Y = Y + ∑' n : ℕ, logCoeff (n + 2) • Y ^ (n + 2) := by
    rw [nearLog, hF.tsum_eq_zero_add]
    simp only [logCoeff_zero, zero_smul, zero_add]
    rw [hF1.tsum_eq_zero_add, e1]
  rw [hsplit, add_sub_cancel_left]
  have hgeo2 : Summable (fun n : ℕ => ‖Y‖ ^ (n + 2)) :=
    (summable_nat_add_iff 2).mpr
      (summable_geometric_of_lt_one (norm_nonneg Y) hY)
  have hnorm_tail :
      Summable (fun n : ℕ => ‖logCoeff (n + 2) • Y ^ (n + 2)‖) :=
    hgeo2.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => norm_logCoeff_smul_pow_le Y (n + 2))
  calc ‖∑' n : ℕ, logCoeff (n + 2) • Y ^ (n + 2)‖
      ≤ ∑' n : ℕ, ‖logCoeff (n + 2) • Y ^ (n + 2)‖ :=
        norm_tsum_le_tsum_norm hnorm_tail
    _ ≤ ∑' n : ℕ, ‖Y‖ ^ (n + 2) :=
        hnorm_tail.tsum_le_tsum
          (fun n => norm_logCoeff_smul_pow_le Y (n + 2)) hgeo2
    _ = ‖Y‖ ^ 2 / (1 - ‖Y‖) := by
        have hre : (fun n : ℕ => ‖Y‖ ^ (n + 2))
            = fun n : ℕ => ‖Y‖ ^ 2 * ‖Y‖ ^ n := by
          funext n; rw [pow_add, mul_comm]
        rw [hre, tsum_mul_left,
          tsum_geometric_of_lt_one (norm_nonneg Y) hY, div_eq_mul_inv]

/-- **Sharp linear bound** (brick M-log-2a, corollary): `‖nearLog Y‖ ≤
‖Y‖/(1-‖Y‖)`.  Unlike `norm_nearLog_le` this **vanishes as `Y → 0`**,
exhibiting `nearLog Y = O(‖Y‖)` (the constant term of the Mercator series
is zero) — the bound the small-field RG analysis actually needs.
Immediate from the linearisation `norm_nearLog_sub_self_le`. -/
theorem norm_nearLog_le_linear {Y : 𝔸} (hY : ‖Y‖ < 1) :
    ‖nearLog Y‖ ≤ ‖Y‖ / (1 - ‖Y‖) := by
  have hne : (1 - ‖Y‖) ≠ 0 := by
    have : (0 : ℝ) < 1 - ‖Y‖ := by linarith
    exact this.ne'
  calc ‖nearLog Y‖ = ‖(nearLog Y - Y) + Y‖ := by congr 1; abel
    _ ≤ ‖nearLog Y - Y‖ + ‖Y‖ := norm_add_le _ _
    _ ≤ ‖Y‖ ^ 2 / (1 - ‖Y‖) + ‖Y‖ := by
        linarith [norm_nearLog_sub_self_le hY]
    _ = ‖Y‖ / (1 - ‖Y‖) := by field_simp; ring

/-- **Scalar correctness of `nearLog`** (brick M-log-2c, non-vacuity
certificate): on the real line the abstract Mercator sum `nearLog`
computes the genuine logarithm, `nearLog (y : ℝ) = Real.log (1 + y)` for
`|y| < 1`.  This proves the abstract construction is **not vacuous** — it
agrees with `Real.log` — and is the commutative base case of the
local-inverse identity (with `Real.exp_log`, `nearLog (Real.exp x - 1)
= x`).  Built on Mathlib's real Mercator series
`Real.hasSum_pow_div_log_of_abs_lt_one`. -/
theorem nearLog_real {y : ℝ} (hy : |y| < 1) :
    nearLog y = Real.log (1 + y) := by
  have hterm : ∀ n : ℕ,
      logCoeff (n + 1) • y ^ (n + 1) = -((-y) ^ (n + 1) / ((n : ℝ) + 1)) := by
    intro n
    have hne : n + 1 ≠ 0 := Nat.succ_ne_zero n
    simp only [logCoeff, if_neg hne, smul_eq_mul]
    push_cast
    ring
  have h0 : HasSum (fun n : ℕ => logCoeff (n + 1) • y ^ (n + 1))
      (Real.log (1 + y)) := by
    have hbase := (Real.hasSum_pow_div_log_of_abs_lt_one
      (x := -y) (by rwa [abs_neg])).neg
    have hval : -(-Real.log (1 - -y)) = Real.log (1 + y) := by
      rw [neg_neg, sub_neg_eq_add]
    rw [hval] at hbase
    have hfe : (fun n : ℕ => logCoeff (n + 1) • y ^ (n + 1))
        = fun n : ℕ => -((-y) ^ (n + 1) / ((n : ℝ) + 1)) := funext hterm
    rw [hfe]; exact hbase
  have hfull : HasSum (fun n : ℕ => logCoeff n • y ^ n) (Real.log (1 + y)) := by
    rw [← hasSum_nat_add_iff' 1]
    simpa using h0
  rw [nearLog]; exact hfull.tsum_eq

/-- **Scalar local-inverse identity** (brick M-log-2c): `nearLog(exp x - 1)
= x` on the real line, for `x < log 2` (so that `exp x - 1 ∈ (-1,1)`).
This is the genuine `log(exp x) = x` identity in the commutative base
case — the scalar instance of the still-open operator brick M-log-2b. -/
theorem nearLog_exp_sub_one_real {x : ℝ} (hx : Real.exp x < 2) :
    nearLog (Real.exp x - 1) = x := by
  have h1 : |Real.exp x - 1| < 1 := by
    rw [abs_lt]
    refine ⟨?_, by linarith⟩
    have := Real.exp_pos x; linarith
  rw [nearLog_real h1,
    show (1 : ℝ) + (Real.exp x - 1) = Real.exp x from by ring, Real.log_exp]

/-- **Conjugation-equivariance of `nearLog`** (brick M-log-3, the
algebraic core of B4-Ū): for a unit `u`,
`nearLog (u·Y·u⁻¹) = u·(nearLog Y)·u⁻¹`.  Conjugation `z ↦ u·z·u⁻¹` is a
continuous linear map, so it commutes with the convergent Mercator
series — this is precisely the input that makes the renormalization-group
field map `Ū` (CMP 109 (0.12)) gauge covariant, and it needs **no**
`log(exp)=id`.  (`‖Y‖<1` ensures the series for `Y` converges; the
conjugated series then converges automatically.) -/
theorem nearLog_conj (u : 𝔸ˣ) {Y : 𝔸} (hY : ‖Y‖ < 1) :
    nearLog ((↑u : 𝔸) * Y * ↑u⁻¹) = (↑u : 𝔸) * nearLog Y * ↑u⁻¹ := by
  have hsum : Summable (fun n : ℕ => logCoeff n • Y ^ n) :=
    summable_logCoeff_smul_pow hY
  have hpow : ∀ n : ℕ,
      ((↑u : 𝔸) * Y * ↑u⁻¹) ^ n = (↑u : 𝔸) * Y ^ n * ↑u⁻¹ := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, ih, pow_succ]
        simp only [mul_assoc]
        rw [← mul_assoc (↑u⁻¹ : 𝔸) (↑u : 𝔸), u.inv_mul, one_mul]
  have hconj : nearLog ((↑u : 𝔸) * Y * ↑u⁻¹)
      = ∑' n : ℕ, (↑u : 𝔸) * (logCoeff n • Y ^ n) * ↑u⁻¹ := by
    rw [nearLog]
    refine tsum_congr (fun n => ?_)
    rw [hpow n, mul_smul_comm, smul_mul_assoc]
  rw [hconj]
  have key := (ContinuousLinearMap.mulLeftRight ℝ 𝔸 (↑u) (↑u⁻¹)).map_tsum hsum
  simp only [ContinuousLinearMap.mulLeftRight_apply] at key
  exact key.symm

/-- **Conjugation-equivariance of the renormalized exponent argument**
(brick M-log-3, the B4-Ū exponent): the weighted sum of near-identity
logarithms appearing in Bałaban's `Ū` (CMP 109 (0.12), the exponent
`L^{-d} Σ_x log(...)`) conjugates as a whole,
`Σ wᵢ • nearLog(u·Yᵢ·u⁻¹) = u · (Σ wᵢ • nearLog Yᵢ) · u⁻¹`.  Lifts
`nearLog_conj` across the finite sum.  Composed with Mathlib's
`NormedSpace.exp_units_conj` (the matching exp law) this gives the gauge
covariance of the full `exp[ Σ … ]` field map — modulo only the carried
analytic linearisation (0.8). -/
theorem nearLog_sum_smul_conj (u : 𝔸ˣ) {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (Y : ι → 𝔸) (hY : ∀ i ∈ s, ‖Y i‖ < 1) :
    ∑ i ∈ s, w i • nearLog ((↑u : 𝔸) * Y i * ↑u⁻¹)
      = (↑u : 𝔸) * (∑ i ∈ s, w i • nearLog (Y i)) * ↑u⁻¹ := by
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [nearLog_conj u (hY i hi), mul_smul_comm, smul_mul_assoc]

/-- `log(1 + 0) = log 1 = 0`. -/
@[simp] theorem nearLog_zero : nearLog (0 : 𝔸) = 0 := by
  have hz : (fun n : ℕ => logCoeff n • (0 : 𝔸) ^ n) = fun _ => 0 := by
    funext n
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · simp [zero_pow h.ne']
  rw [nearLog, hz, tsum_zero]

end YangMills.RG
