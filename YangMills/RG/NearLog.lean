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

open scoped BigOperators Nat

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

/-- **Reverse comparison with the Mercator tail.**  Since
`nearLog Y = Y + O(‖Y‖²)`, the original identity deviation is controlled by the
logarithmic coordinate plus the same quadratic tail:
`‖Y‖ ≤ ‖nearLog Y‖ + ‖Y‖²/(1-‖Y‖)`.

This is the raw form of the near-identity dictionary converting geometric
smallness of a group deviation `D - 1` and analytic smallness of
`nearLog (D - 1)`. -/
theorem norm_self_le_norm_nearLog_add_tail {Y : 𝔸} (hY : ‖Y‖ < 1) :
    ‖Y‖ ≤ ‖nearLog Y‖ + ‖Y‖ ^ 2 / (1 - ‖Y‖) := by
  calc ‖Y‖ = ‖nearLog Y - (nearLog Y - Y)‖ := by congr 1; abel
    _ ≤ ‖nearLog Y‖ + ‖nearLog Y - Y‖ := norm_sub_le _ _
    _ ≤ ‖nearLog Y‖ + ‖Y‖ ^ 2 / (1 - ‖Y‖) := by
        gcongr
        exact norm_nearLog_sub_self_le hY

/-- **Near-identity dictionary, geometric coordinate from logarithmic coordinate.**
For `‖Y‖ ≤ 1/3`, the Mercator logarithm is bi-Lipschitz at the coarse constant
level: `‖Y‖ ≤ 2‖nearLog Y‖`.

The constant is intentionally non-sharp; it is the robust cutoff conversion used
when translating a small holonomy deviation `D - 1` into Bałaban's analytic
logarithmic coordinate. -/
theorem norm_self_le_two_norm_nearLog_of_norm_le_third {Y : 𝔸}
    (hY : ‖Y‖ ≤ 1 / 3) :
    ‖Y‖ ≤ 2 * ‖nearLog Y‖ := by
  have hYlt : ‖Y‖ < 1 := by linarith [norm_nonneg Y]
  have hbase := norm_self_le_norm_nearLog_add_tail hYlt
  have htail : ‖Y‖ ^ 2 / (1 - ‖Y‖) ≤ ‖Y‖ / 2 := by
    have hden : 0 < 1 - ‖Y‖ := by linarith [norm_nonneg Y]
    field_simp [hden.ne']
    nlinarith [norm_nonneg Y, hY]
  linarith

/-- **Near-identity dictionary, logarithmic coordinate from geometric coordinate.**
For `‖Y‖ ≤ 1/2`, the logarithmic coordinate is controlled by the geometric
deviation: `‖nearLog Y‖ ≤ 2‖Y‖`. -/
theorem norm_nearLog_le_two_norm_self_of_norm_le_half {Y : 𝔸}
    (hY : ‖Y‖ ≤ 1 / 2) :
    ‖nearLog Y‖ ≤ 2 * ‖Y‖ := by
  have hYlt : ‖Y‖ < 1 := by linarith [norm_nonneg Y]
  have hlin := norm_nearLog_le_linear hYlt
  have hfrac : ‖Y‖ / (1 - ‖Y‖) ≤ 2 * ‖Y‖ := by
    have hden : 0 < 1 - ‖Y‖ := by linarith [norm_nonneg Y]
    field_simp [hden.ne']
    nlinarith [norm_nonneg Y, hY]
  exact le_trans hlin hfrac

/-- **Two-sided near-identity dictionary.**  In the small ball `‖Y‖ ≤ 1/3`,
`Y` and `nearLog Y` control each other up to the fixed constant `2`.

For the lattice gauge application one substitutes
`Y = rep(UbarDeviation ...).val - 1`, the faithful argument of `nearLog`.
This is deliberately a local analytic comparison, not a claim about the full
Bałaban `T`-operation or large-field measure decomposition. -/
theorem norm_nearLog_two_sided_of_norm_le_third {Y : 𝔸} (hY : ‖Y‖ ≤ 1 / 3) :
    ‖Y‖ ≤ 2 * ‖nearLog Y‖ ∧ ‖nearLog Y‖ ≤ 2 * ‖Y‖ := by
  refine ⟨norm_self_le_two_norm_nearLog_of_norm_le_third hY, ?_⟩
  exact norm_nearLog_le_two_norm_self_of_norm_le_half (by linarith)

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

/-- **Gauge covariance of the abstract `Ū`-block** (brick B4-Ū, algebra
level): Bałaban's renormalized field element (CMP 109 (0.12) shape)
`Ū = exp[ Σ wᵢ • nearLog(deviationᵢ) ] · g` is gauge covariant — under
the gauge action conjugating the base `g` and every deviation `Yᵢ` by a
unit `u`, the whole block conjugates,
`exp[Σ wᵢ•nearLog(u·Yᵢ·u⁻¹)]·(u·g·u⁻¹) = u·(exp[Σ wᵢ•nearLog Yᵢ]·g)·u⁻¹`.
Assembled from `nearLog_sum_smul_conj` and Mathlib's
`NormedSpace.exp_units_conj`; **no** `log(exp)=id` is used (covariance is
purely conjugation-equivariance).  This is the gauge covariance the
M3-assembly's §6.3 input ultimately requires of the RG transformation. -/
theorem UbarBlock_conj [NormedAlgebra ℚ 𝔸] (u g : 𝔸ˣ) {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (Y : ι → 𝔸) (hY : ∀ i ∈ s, ‖Y i‖ < 1) :
    NormedSpace.exp (∑ i ∈ s, w i • nearLog ((↑u : 𝔸) * Y i * ↑u⁻¹))
        * ((↑u : 𝔸) * ↑g * ↑u⁻¹)
      = (↑u : 𝔸)
        * (NormedSpace.exp (∑ i ∈ s, w i • nearLog (Y i)) * ↑g) * ↑u⁻¹ := by
  rw [nearLog_sum_smul_conj u s w Y hY, NormedSpace.exp_units_conj]
  simp only [mul_assoc]
  rw [← mul_assoc (↑u⁻¹ : 𝔸) (↑u : 𝔸), u.inv_mul, one_mul]

/-- Termwise geometric bound for the exponential series:
`‖(n!)⁻¹ • Z^n‖ ≤ ‖Z‖^n` (`(n!)⁻¹ ≤ 1` and `‖Z^n‖ ≤ ‖Z‖^n`). -/
theorem norm_expTerm_le [NormOneClass 𝔸] (Z : 𝔸) (n : ℕ) :
    ‖((n ! : ℝ)⁻¹) • Z ^ n‖ ≤ ‖Z‖ ^ n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hpos : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast n.factorial_pos
    have hfac : (1 : ℝ) ≤ (n ! : ℝ) := by exact_mod_cast n.factorial_pos
    have hcoeff : ((n ! : ℝ)⁻¹) ≤ 1 := by rw [inv_le_one₀ hpos]; exact hfac
    calc ((n ! : ℝ)⁻¹) * ‖Z ^ n‖
        ≤ 1 * ‖Z‖ ^ n :=
          mul_le_mul hcoeff (norm_pow_le' Z h) (norm_nonneg _) zero_le_one
      _ = ‖Z‖ ^ n := one_mul _

/-- **Second-order remainder of the operator exponential** (brick
M-log-4): `NormedSpace.exp Z = 1 + Z + O(‖Z‖²)`, quantitatively
`‖exp Z - 1 - Z‖ ≤ ‖Z‖²/(1-‖Z‖)` for `‖Z‖<1`.  Proved directly from the
`n ≥ 2` tail of the exponential series (`NormedSpace.exp_eq_tsum ℝ`),
mirroring `norm_nearLog_sub_self_le`.  Together with that linearisation
of `nearLog`, this gives `exp(nearLog Y) = 1 + Y + O(‖Y‖²)` — the genuine
linearisation content of Bałaban's (0.8) (the RG map is the identity to
first order) **without** the exact local-inverse identity `log(exp)=id`. -/
theorem norm_exp_sub_one_sub_self_le [NormOneClass 𝔸] {Z : 𝔸} (hZ : ‖Z‖ < 1) :
    ‖NormedSpace.exp Z - 1 - Z‖ ≤ ‖Z‖ ^ 2 / (1 - ‖Z‖) := by
  have hsum : Summable (fun n : ℕ => ((n ! : ℝ)⁻¹) • Z ^ n) :=
    Summable.of_norm_bounded (g := fun n => ‖Z‖ ^ n)
      (summable_geometric_of_lt_one (norm_nonneg Z) hZ) (norm_expTerm_le Z)
  have hF1 : Summable (fun n : ℕ => (((n + 1)! : ℝ)⁻¹) • Z ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr hsum
  have e0 : ((0 ! : ℝ)⁻¹) • Z ^ 0 = (1 : 𝔸) := by simp
  have e1 : (((0 + 1)! : ℝ)⁻¹) • Z ^ (0 + 1) = Z := by simp
  have hexp : NormedSpace.exp Z = ∑' n : ℕ, ((n ! : ℝ)⁻¹) • Z ^ n := by
    rw [NormedSpace.exp_eq_tsum ℝ]
  have hsplit : NormedSpace.exp Z
      = 1 + (Z + ∑' n : ℕ, (((n + 2)! : ℝ)⁻¹) • Z ^ (n + 2)) := by
    rw [hexp, hsum.tsum_eq_zero_add, e0, hF1.tsum_eq_zero_add, e1]
  rw [hsplit, add_sub_cancel_left, add_sub_cancel_left]
  have hgeo2 : Summable (fun n : ℕ => ‖Z‖ ^ (n + 2)) :=
    (summable_nat_add_iff 2).mpr
      (summable_geometric_of_lt_one (norm_nonneg Z) hZ)
  have hnorm_tail :
      Summable (fun n : ℕ => ‖(((n + 2)! : ℝ)⁻¹) • Z ^ (n + 2)‖) :=
    hgeo2.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => norm_expTerm_le Z (n + 2))
  calc ‖∑' n : ℕ, (((n + 2)! : ℝ)⁻¹) • Z ^ (n + 2)‖
      ≤ ∑' n : ℕ, ‖(((n + 2)! : ℝ)⁻¹) • Z ^ (n + 2)‖ :=
        norm_tsum_le_tsum_norm hnorm_tail
    _ ≤ ∑' n : ℕ, ‖Z‖ ^ (n + 2) :=
        hnorm_tail.tsum_le_tsum (fun n => norm_expTerm_le Z (n + 2)) hgeo2
    _ = ‖Z‖ ^ 2 / (1 - ‖Z‖) := by
        have hre : (fun n : ℕ => ‖Z‖ ^ (n + 2))
            = fun n : ℕ => ‖Z‖ ^ 2 * ‖Z‖ ^ n := by
          funext n; rw [pow_add, mul_comm]
        rw [hre, tsum_mul_left,
          tsum_geometric_of_lt_one (norm_nonneg Z) hZ, div_eq_mul_inv]

/-- **The renormalization-group map linearises to the identity** (brick
M-log-5, the quantitative form of Bałaban's axiom (0.8)): for `‖Y‖<1/2`,
`exp(nearLog Y) = 1 + Y + O(‖Y‖²)`, with the remainder bounded explicitly
by the two second-order tails,
`‖exp(nearLog Y) - 1 - Y‖ ≤ ‖nearLog Y‖²/(1-‖nearLog Y‖) + ‖Y‖²/(1-‖Y‖)`.
Assembled by the triangle inequality from the exp remainder (M-log-4)
and the `nearLog` remainder (M-log-2a); `‖nearLog Y‖<1` is discharged
from `‖Y‖<1/2` via the sharp bound (M-log-2a′).  This is the genuine
content of (0.8) — the RG field map is the identity to first order plus
a quadratic correction — obtained **without** the exact local-inverse
identity `log(exp)=id`. -/
theorem norm_exp_nearLog_sub_one_sub_self_le [NormOneClass 𝔸] {Y : 𝔸}
    (hY : ‖Y‖ < 1 / 2) :
    ‖NormedSpace.exp (nearLog Y) - 1 - Y‖
      ≤ ‖nearLog Y‖ ^ 2 / (1 - ‖nearLog Y‖) + ‖Y‖ ^ 2 / (1 - ‖Y‖) := by
  have hY1 : ‖Y‖ < 1 := by linarith
  have hnl : ‖nearLog Y‖ < 1 := by
    have hb := norm_nearLog_le_linear hY1
    have hlt : ‖Y‖ / (1 - ‖Y‖) < 1 := by
      rw [div_lt_one (by linarith)]; linarith
    linarith
  have hdecomp : NormedSpace.exp (nearLog Y) - 1 - Y
      = (NormedSpace.exp (nearLog Y) - 1 - nearLog Y) + (nearLog Y - Y) := by
    abel
  rw [hdecomp]
  calc ‖(NormedSpace.exp (nearLog Y) - 1 - nearLog Y) + (nearLog Y - Y)‖
      ≤ ‖NormedSpace.exp (nearLog Y) - 1 - nearLog Y‖ + ‖nearLog Y - Y‖ :=
        norm_add_le _ _
    _ ≤ ‖nearLog Y‖ ^ 2 / (1 - ‖nearLog Y‖) + ‖Y‖ ^ 2 / (1 - ‖Y‖) := by
        gcongr
        · exact norm_exp_sub_one_sub_self_le hnl
        · exact norm_nearLog_sub_self_le hY1

/-- **Small-field stability of the renormalized field** (U1 ingredient):
the renormalized deviation `exp(nearLog Y) - 1` is controlled by the
original deviation `Y`, namely `‖exp(nearLog Y) - 1‖ ≤ ‖Y‖ + O(‖Y‖²)`
for `‖Y‖<1/2` — to leading order the renormalized deviation equals the
original, so the small-field region is preserved under the
`exp ∘ nearLog` step.  Immediate from the linearisation (M-log-5) by the
triangle inequality.  This is the boundedness Bałaban's small-field
single-scale bound (UV plan U1) is built on. -/
theorem norm_exp_nearLog_sub_one_le [NormOneClass 𝔸] {Y : 𝔸}
    (hY : ‖Y‖ < 1 / 2) :
    ‖NormedSpace.exp (nearLog Y) - 1‖
      ≤ ‖Y‖ + (‖nearLog Y‖ ^ 2 / (1 - ‖nearLog Y‖) + ‖Y‖ ^ 2 / (1 - ‖Y‖)) := by
  calc ‖NormedSpace.exp (nearLog Y) - 1‖
      = ‖(NormedSpace.exp (nearLog Y) - 1 - Y) + Y‖ := by congr 1; abel
    _ ≤ ‖NormedSpace.exp (nearLog Y) - 1 - Y‖ + ‖Y‖ := norm_add_le _ _
    _ ≤ (‖nearLog Y‖ ^ 2 / (1 - ‖nearLog Y‖) + ‖Y‖ ^ 2 / (1 - ‖Y‖)) + ‖Y‖ := by
        have h := norm_exp_nearLog_sub_one_sub_self_le hY
        linarith
    _ = ‖Y‖ + (‖nearLog Y‖ ^ 2 / (1 - ‖nearLog Y‖) + ‖Y‖ ^ 2 / (1 - ‖Y‖)) := by
        ring

/-- `log(1 + 0) = log 1 = 0`. -/
@[simp] theorem nearLog_zero : nearLog (0 : 𝔸) = 0 := by
  have hz : (fun n : ℕ => logCoeff n • (0 : 𝔸) ^ n) = fun _ => 0 := by
    funext n
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · simp [zero_pow h.ne']
  rw [nearLog, hz, tsum_zero]

end YangMills.RG
