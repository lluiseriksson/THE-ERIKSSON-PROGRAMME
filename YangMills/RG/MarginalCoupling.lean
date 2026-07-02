/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.RG.CouplingFlow

/-!
# Marginal-coupling scale-series summability (gauge-RG, the YM coupling flow)

`docs/BALABAN-SOURCE-BOUNDS.md`.  In **4D Yang–Mills** the running coupling
`g_k` is **marginal / asymptotically free**: it runs only **logarithmically**,
NOT geometrically.  A geometric bound `g_k ≤ C·rᵏ` (`r < 1`) — which holds for
*irrelevant* couplings in superrenormalizable models like Dimock's φ⁴₃ — is
**false** for the marginal YM coupling.  (This is the load-bearing correction
flagged across the Balaban source review: geometric `rᵏ` factors in Balaban
multiply irrelevant remainders, never the marginal coupling itself.)

This file shows that, despite the absence of geometric decay, the
**renormalization-remainder series over scales is still summable** when the
activity power `κ₀ > 1`:

* **`marginal_coupling_le_recip_affine`** — the inverse-coupling lower bound
  `1/g₀ + β·n ≤ 1/gₙ` is converted into the pointwise usable upper bound
  `gₙ ≤ 1/(1/g₀ + β·n)`.
* **`marginal_coupling_le_recip_affine_of_recursion`** — the same upper bound
  directly from the marginal recursion `g_{k+1} = g_k(1 − β g_k)`.
* **`marginal_coupling_pow_le_recip_affine`** — the activity profile obeys the
  corresponding power bound for every nonnegative exponent.
* **`marginal_coupling_pow_summable`** — from the asymptotic-freedom lower
  bound `1/g₀ + β·n ≤ 1/gₙ` (the conclusion of
  `inv_coupling_linear_growth`), `β > 0`, and `κ₀ > 1`, the series
  `∑ₙ gₙ^{κ₀}` converges.  Proof: `gₙ ≤ 1/(c(n+1))`, then comparison with
  the convergent `p`-series `∑ n^{−κ₀}`.
* **`marginal_coupling_tendsto_zero`** — asymptotic freedom proper: `gₙ → 0`.
* **`marginal_coupling_pow_summable_of_recursion`** — the same summability
  directly from the marginal recursion `g_{k+1} = g_k(1 − β g_k)`.
* **`marginal_coupling_remainder_tsum_le_of_recursion`** — the scale-summed
  remainder bound with the former external summability premise discharged by
  the marginal recursion.

This replaces, for the YM `hRpoly` coupling side, the (model-incorrect)
geometric `hg : g_k ≤ C·rᵏ` of `lattice_mass_gap_of_cluster_and_coupling`
with the **honest marginal-coupling summability**.  It does NOT supply the YM
activity-decay bound itself (Balaban CMP 116 Lemma 3 / Large Field II — a
carried analytic input; see `BALABAN-SOURCE-BOUNDS.md`).

**Source.**  Bałaban CMP 109 (the recursive coupling renormalization / β-
functions, marginal in 4D); the p-series comparison is elementary; asymptotic
freedom of pure SU(N).  Strategy/framing Lluis Eriksson (ai.viXra:2602.0088).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

open scoped BigOperators

namespace YangMills.RG

/-- **Robust marginal one-step with cubic error.**  If one marginal step is
within a cubic error of `x - beta * x^2`, and the product-form smallness
`C * x <= beta / 2`, `3 * beta * x <= 1` holds, then that step remains
positive and still gains at least half of the quadratic decrement.

This is the PR0 local brick for perturbing the exact marginal recursion; it
does not assert a global source theorem or any activity-decay statement. -/
lemma robust_marginal_cubic_error_step_bounds {beta C x y : ℝ}
    (_hbeta : 0 < beta) (_hC : 0 ≤ C) (hx : 0 < x)
    (hCsmall : C * x ≤ beta / 2) (hbetasmall : 3 * beta * x ≤ 1)
    (hstep : |y - (x - beta * x ^ 2)| ≤ C * x ^ 3) :
    0 < y ∧ y ≤ x - (beta / 2) * x ^ 2 := by
  have hx0 : 0 ≤ x := hx.le
  have hx2_nonneg : 0 ≤ x ^ 2 := sq_nonneg x
  have hCx3 : C * x ^ 3 ≤ (beta / 2) * x ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hCsmall hx2_nonneg
    nlinarith [hx]
  have hupper_abs : y - (x - beta * x ^ 2) ≤ C * x ^ 3 := (abs_le.mp hstep).2
  have hlower_abs : -(C * x ^ 3) ≤ y - (x - beta * x ^ 2) := (abs_le.mp hstep).1
  have hupper : y ≤ x - (beta / 2) * x ^ 2 := by
    nlinarith
  have hpos_lower : x - (3 * beta / 2) * x ^ 2 ≤ y := by
    nlinarith
  have hpos_aux : 0 < x - (3 * beta / 2) * x ^ 2 := by
    nlinarith
  exact ⟨lt_of_lt_of_le hpos_aux hpos_lower, hupper⟩

/-- Reciprocal growth from a robust one-step marginal decrement. -/
lemma robust_marginal_reciprocal_step {beta x y : ℝ}
    (hbeta : 0 < beta) (hx : 0 < x) (hy : 0 < y)
    (hdec : y ≤ x - (beta / 2) * x ^ 2) :
    1 / x + beta / 2 ≤ 1 / y := by
  have hcoef : 0 ≤ 1 / x + beta / 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hdec hcoef
  rw [le_div_iff₀ hy]
  have hexp : (1 / x + beta / 2) * (x - (beta / 2) * x ^ 2) =
      1 - (beta / 2 * x) ^ 2 := by
    field_simp [hx.ne']
    ring
  calc (1 / x + beta / 2) * y
      ≤ (1 / x + beta / 2) * (x - (beta / 2) * x ^ 2) := hmul
    _ = 1 - (beta / 2 * x) ^ 2 := hexp
    _ ≤ 1 := by nlinarith [sq_nonneg (beta / 2 * x)]

/-- **Robust marginal cubic-error invariant.**  Under the product-form
smallness hypotheses from PR0, the perturbed marginal recursion preserves
positivity, stays below the initial coupling, and gains inverse coupling at
rate `beta / 2`.

This is an invariant theorem only for the abstract cubic-error recursion; it
does not consume or promote any source/database field. -/
theorem robust_marginal_cubic_error_inverse_growth (g : ℕ → ℝ) {beta C : ℝ}
    (hbeta : 0 < beta) (hC : 0 ≤ C) (hg0 : 0 < g 0)
    (hCsmall : C * g 0 ≤ beta / 2) (hbetasmall : 3 * beta * g 0 ≤ 1)
    (hstep : ∀ k,
      |g (k + 1) - (g k - beta * g k ^ 2)| ≤ C * g k ^ 3) :
    ∀ k : ℕ,
      0 < g k ∧ g k ≤ g 0 ∧ 1 / g 0 + (beta / 2) * (k : ℝ) ≤ 1 / g k := by
  intro k
  induction k with
  | zero =>
      exact ⟨hg0, le_rfl, by simp⟩
  | succ k ih =>
      rcases ih with ⟨hgk_pos, hgk_le, hAFk⟩
      have hCsmall_k : C * g k ≤ beta / 2 :=
        (mul_le_mul_of_nonneg_left hgk_le hC).trans hCsmall
      have hbetasmall_k : 3 * beta * g k ≤ 1 := by
        have hcoef : 0 ≤ 3 * beta := by positivity
        exact (mul_le_mul_of_nonneg_left hgk_le hcoef).trans hbetasmall
      have hbounds := robust_marginal_cubic_error_step_bounds
        (beta := beta) (C := C) (x := g k) (y := g (k + 1))
        hbeta hC hgk_pos hCsmall_k hbetasmall_k (hstep k)
      rcases hbounds with ⟨hnext_pos, hnext_dec⟩
      have hnext_le_gk : g (k + 1) ≤ g k := by
        have hquad_nonneg : 0 ≤ (beta / 2) * g k ^ 2 :=
          mul_nonneg (by positivity) (sq_nonneg _)
        linarith
      have hnext_le_g0 : g (k + 1) ≤ g 0 := hnext_le_gk.trans hgk_le
      have hrecip_step :
          1 / g k + beta / 2 ≤ 1 / g (k + 1) :=
        robust_marginal_reciprocal_step hbeta hgk_pos hnext_pos hnext_dec
      have hAFnext :
          1 / g 0 + (beta / 2) * ((k + 1 : ℕ) : ℝ) ≤ 1 / g (k + 1) := by
        calc 1 / g 0 + (beta / 2) * ((k + 1 : ℕ) : ℝ)
            = (1 / g 0 + (beta / 2) * (k : ℝ)) + beta / 2 := by
              push_cast
              ring
          _ ≤ 1 / g k + beta / 2 := by linarith
          _ ≤ 1 / g (k + 1) := hrecip_step
      exact ⟨hnext_pos, hnext_le_g0, hAFnext⟩

/-- **Pointwise marginal-coupling upper bound.**  The asymptotic-freedom lower
bound on inverse coupling, `1/g₀ + β·n ≤ 1/gₙ`, is equivalent to the usable
upper bound `gₙ ≤ 1/(1/g₀ + β·n)` when the coupling is positive and `β ≥ 0`.

This theorem names the algebraic step that downstream UV estimates actually
consume, so they no longer need to reprove the reciprocal conversion locally. -/
theorem marginal_coupling_le_recip_affine (g : ℕ → ℝ) {β : ℝ}
    (hβ : 0 ≤ β) (hpos : ∀ k, 0 < g k)
    (hAF : ∀ n : ℕ, 1 / g 0 + β * (n : ℝ) ≤ 1 / g n) :
    ∀ n : ℕ, g n ≤ 1 / (1 / g 0 + β * (n : ℝ)) := by
  intro n
  have hden : (0 : ℝ) < 1 / g 0 + β * (n : ℝ) := by
    have h0 : (0 : ℝ) < 1 / g 0 := one_div_pos.mpr (hpos 0)
    have hn : (0 : ℝ) ≤ β * (n : ℝ) := mul_nonneg hβ (Nat.cast_nonneg n)
    linarith
  have h1 : g n * (1 / g 0 + β * (n : ℝ)) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left (hAF n) (hpos n).le
    rwa [mul_one_div, div_self (hpos n).ne'] at this
  exact (le_div_iff₀ hden).mpr h1

/-- **Pointwise marginal-coupling upper bound from the recursion.**  The
logistic marginal RG recursion first gives inverse-coupling growth via
`inv_coupling_linear_growth`; the reciprocal conversion is then theorem-fed by
`marginal_coupling_le_recip_affine`. -/
theorem marginal_coupling_le_recip_affine_of_recursion (g : ℕ → ℝ) {β : ℝ}
    (hβ : 0 ≤ β) (hpos : ∀ k, 0 < g k) (hsmall : ∀ k, β * g k < 1)
    (hrec : ∀ k, g (k + 1) = g k * (1 - β * g k)) :
    ∀ n : ℕ, g n ≤ 1 / (1 / g 0 + β * (n : ℝ)) :=
  marginal_coupling_le_recip_affine g hβ hpos
    (inv_coupling_linear_growth g hβ hpos hsmall hrec)

/-- Power version of `marginal_coupling_le_recip_affine`: the marginal activity
profile `gₙ^κ₀` is bounded by the explicit logarithmic profile whenever
`κ₀ ≥ 0`. -/
theorem marginal_coupling_pow_le_recip_affine (g : ℕ → ℝ) {β κ₀ : ℝ}
    (hβ : 0 ≤ β) (hpos : ∀ k, 0 < g k)
    (hAF : ∀ n : ℕ, 1 / g 0 + β * (n : ℝ) ≤ 1 / g n)
    (hκ : 0 ≤ κ₀) :
    ∀ n : ℕ,
      g n ^ κ₀ ≤ (1 / (1 / g 0 + β * (n : ℝ))) ^ κ₀ := by
  intro n
  exact Real.rpow_le_rpow (hpos n).le
    (marginal_coupling_le_recip_affine g hβ hpos hAF n) hκ

/-- Power marginal-coupling upper bound from the logistic recursion. -/
theorem marginal_coupling_pow_le_recip_affine_of_recursion
    (g : ℕ → ℝ) {β κ₀ : ℝ}
    (hβ : 0 ≤ β) (hpos : ∀ k, 0 < g k) (hsmall : ∀ k, β * g k < 1)
    (hrec : ∀ k, g (k + 1) = g k * (1 - β * g k))
    (hκ : 0 ≤ κ₀) :
    ∀ n : ℕ,
      g n ^ κ₀ ≤ (1 / (1 / g 0 + β * (n : ℝ))) ^ κ₀ :=
  marginal_coupling_pow_le_recip_affine g hβ hpos
    (inv_coupling_linear_growth g hβ hpos hsmall hrec) hκ

/-- **Marginal (asymptotically-free) coupling gives a summable scale-series.**
If the running coupling obeys the asymptotic-freedom lower bound
`1/g₀ + β·n ≤ 1/gₙ` (the conclusion of `inv_coupling_linear_growth`, i.e. the
4D marginal recursion — NOT geometric decay), with `β > 0` and `κ₀ > 1`, then
`∑ₙ gₙ^{κ₀}` converges.  So although the marginal YM coupling does **not**
decay geometrically (`gₖ ≤ C·rᵏ` is false), the renormalization remainder
series over scales is still summable provided the activity power `κ₀ > 1`.
Comparison with the `p`-series `∑ n^{−κ₀}` via `gₙ ≤ 1/(c(n+1))`. -/
theorem marginal_coupling_pow_summable (g : ℕ → ℝ) {β κ₀ : ℝ}
    (hβ : 0 < β) (hpos : ∀ k, 0 < g k)
    (hAF : ∀ n : ℕ, 1 / g 0 + β * (n : ℝ) ≤ 1 / g n) (hκ : 1 < κ₀) :
    Summable (fun n => g n ^ κ₀) := by
  have hg0 : 0 < g 0 := hpos 0
  set c : ℝ := min (1 / g 0) β with hcdef
  have hc0 : 0 < c := lt_min (by positivity) hβ
  have hmaj : Summable (fun n : ℕ => (c ^ κ₀)⁻¹ * (((n : ℝ) + 1) ^ κ₀)⁻¹) := by
    apply Summable.mul_left
    have hp : Summable (fun n : ℕ => ((n : ℝ) ^ κ₀)⁻¹) := Real.summable_nat_rpow_inv.mpr hκ
    have := (summable_nat_add_iff 1).mpr hp
    simpa using this
  refine Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (hpos n).le _)
    (fun n => ?_) hmaj
  have hgle : g n ≤ 1 / (1 / g 0 + β * (n : ℝ)) :=
    marginal_coupling_le_recip_affine g hβ.le hpos hAF n
  have hclb : c * ((n : ℝ) + 1) ≤ 1 / g 0 + β * (n : ℝ) := by
    have h2 : c ≤ 1 / g 0 := min_le_left _ _
    have h3 : c ≤ β := min_le_right _ _
    have h4 : c * (n : ℝ) ≤ β * (n : ℝ) := mul_le_mul_of_nonneg_right h3 (Nat.cast_nonneg n)
    nlinarith [h2, h4]
  have hcn : (0 : ℝ) < c * ((n : ℝ) + 1) := by positivity
  have hgle2 : g n ≤ 1 / (c * ((n : ℝ) + 1)) :=
    le_trans hgle (one_div_le_one_div_of_le hcn hclb)
  calc g n ^ κ₀
      ≤ (1 / (c * ((n : ℝ) + 1))) ^ κ₀ :=
        Real.rpow_le_rpow (hpos n).le hgle2 (by linarith)
    _ = (c ^ κ₀)⁻¹ * (((n : ℝ) + 1) ^ κ₀)⁻¹ := by
        rw [one_div, Real.inv_rpow hcn.le, Real.mul_rpow hc0.le (by positivity), mul_inv]

/-- Logarithmic decay extracted from the robust cubic-error invariant. -/
theorem robust_marginal_cubic_error_decay (g : ℕ → ℝ) {beta C : ℝ}
    (hbeta : 0 < beta) (hC : 0 ≤ C) (hg0 : 0 < g 0)
    (hCsmall : C * g 0 ≤ beta / 2) (hbetasmall : 3 * beta * g 0 ≤ 1)
    (hstep : ∀ k,
      |g (k + 1) - (g k - beta * g k ^ 2)| ≤ C * g k ^ 3) :
    ∀ k : ℕ, 1 ≤ k → g k ≤ 2 / (beta * (k : ℝ)) := by
  intro k hk
  have hinv := robust_marginal_cubic_error_inverse_growth g hbeta hC hg0
    hCsmall hbetasmall hstep
  have hpos : ∀ n, 0 < g n := fun n => (hinv n).1
  have hAF : ∀ n : ℕ, 1 / g 0 + (beta / 2) * (n : ℝ) ≤ 1 / g n :=
    fun n => (hinv n).2.2
  have hgle : g k ≤ 1 / (1 / g 0 + (beta / 2) * (k : ℝ)) :=
    marginal_coupling_le_recip_affine g (by positivity) hpos hAF k
  have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.succ_le_iff.mp hk
  have hden0 : 0 < (beta / 2) * (k : ℝ) := by positivity
  have hden_le : (beta / 2) * (k : ℝ) ≤ 1 / g 0 + (beta / 2) * (k : ℝ) := by
    have hg0inv : 0 ≤ 1 / g 0 := by positivity
    linarith
  calc g k
      ≤ 1 / (1 / g 0 + (beta / 2) * (k : ℝ)) := hgle
    _ ≤ 1 / ((beta / 2) * (k : ℝ)) := by
      exact one_div_le_one_div_of_le hden0 hden_le
    _ = 2 / (beta * (k : ℝ)) := by
      field_simp [hbeta.ne', hkpos.ne']

/-- Square summability extracted from the robust cubic-error invariant. -/
theorem robust_marginal_cubic_error_rpow_two_summable
    (g : ℕ → ℝ) {beta C : ℝ}
    (hbeta : 0 < beta) (hC : 0 ≤ C) (hg0 : 0 < g 0)
    (hCsmall : C * g 0 ≤ beta / 2) (hbetasmall : 3 * beta * g 0 ≤ 1)
    (hstep : ∀ k,
      |g (k + 1) - (g k - beta * g k ^ 2)| ≤ C * g k ^ 3) :
    Summable (fun k => g k ^ (2 : ℝ)) := by
  have hinv := robust_marginal_cubic_error_inverse_growth g hbeta hC hg0
    hCsmall hbetasmall hstep
  exact marginal_coupling_pow_summable g (by positivity) (fun k => (hinv k).1)
    (fun k => (hinv k).2.2) (by norm_num)

/-- Power summability extracted from the robust cubic-error invariant. -/
theorem robust_marginal_cubic_error_rpow_summable
    (g : ℕ → ℝ) {beta C kappa : ℝ}
    (hbeta : 0 < beta) (hC : 0 ≤ C) (hg0 : 0 < g 0)
    (hCsmall : C * g 0 ≤ beta / 2) (hbetasmall : 3 * beta * g 0 ≤ 1)
    (hstep : ∀ k,
      |g (k + 1) - (g k - beta * g k ^ 2)| ≤ C * g k ^ 3)
    (hkappa : 1 < kappa) :
    Summable (fun k => g k ^ kappa) := by
  have hinv := robust_marginal_cubic_error_inverse_growth g hbeta hC hg0
    hCsmall hbetasmall hstep
  exact marginal_coupling_pow_summable g (by positivity) (fun k => (hinv k).1)
    (fun k => (hinv k).2.2) hkappa

/-- Concrete non-vacuity witness for the robust cubic-error recursion. -/
noncomputable def robustMarginalCubicWitness (k : ℕ) : ℝ := 1 / ((k : ℝ) + 4)

/-- The concrete witness `g k = 1 / (k + 4)` satisfies the cubic-error step
with `beta = 1` and `C = 1`. -/
theorem robustMarginalCubicWitness_step (k : ℕ) :
    |robustMarginalCubicWitness (k + 1) -
      (robustMarginalCubicWitness k -
        (1 : ℝ) * robustMarginalCubicWitness k ^ 2)| ≤
        (1 : ℝ) * robustMarginalCubicWitness k ^ 3 := by
  dsimp [robustMarginalCubicWitness]
  have hk4 : (0 : ℝ) < (k : ℝ) + 4 := by positivity
  have hk5 : (0 : ℝ) < (k : ℝ) + 5 := by positivity
  have hcalc :
      1 / ((k : ℝ) + 1 + 4) -
          (1 / ((k : ℝ) + 4) - 1 * (1 / ((k : ℝ) + 4)) ^ 2) =
        1 / (((k : ℝ) + 4) ^ 2 * ((k : ℝ) + 5)) := by
    field_simp [hk4.ne', hk5.ne']
    ring
  have hcalc' :
      1 / (↑(k + 1) + 4) -
          (1 / ((k : ℝ) + 4) - 1 * (1 / ((k : ℝ) + 4)) ^ 2) =
        1 / (((k : ℝ) + 4) ^ 2 * ((k : ℝ) + 5)) := by
    simpa [Nat.cast_add, Nat.cast_one, add_assoc] using hcalc
  rw [hcalc']
  rw [abs_of_nonneg]
  · rw [one_mul]
    have hden_le :
        ((k : ℝ) + 4) ^ 3 ≤ ((k : ℝ) + 4) ^ 2 * ((k : ℝ) + 5) := by
      have hsq : 0 ≤ ((k : ℝ) + 4) ^ 2 := sq_nonneg _
      have h45 : (k : ℝ) + 4 ≤ (k : ℝ) + 5 := by norm_num
      nlinarith [mul_le_mul_of_nonneg_left h45 hsq]
    calc 1 / (((k : ℝ) + 4) ^ 2 * ((k : ℝ) + 5))
        ≤ 1 / (((k : ℝ) + 4) ^ 3) := one_div_le_one_div_of_le (by positivity) hden_le
      _ = (1 / ((k : ℝ) + 4)) ^ 3 := by
        field_simp [hk4.ne']
  · positivity

/-- The concrete witness satisfies the PR0 inverse-growth invariant, so the
robust theorem has a nonempty hypothesis surface. -/
theorem robustMarginalCubicWitness_invariant :
    ∀ k : ℕ,
      0 < robustMarginalCubicWitness k ∧
        robustMarginalCubicWitness k ≤ robustMarginalCubicWitness 0 ∧
          1 / robustMarginalCubicWitness 0 + ((1 : ℝ) / 2) * (k : ℝ) ≤
            1 / robustMarginalCubicWitness k := by
  exact robust_marginal_cubic_error_inverse_growth robustMarginalCubicWitness
    (beta := 1) (C := 1) (by norm_num) (by norm_num)
    (by norm_num [robustMarginalCubicWitness])
    (by norm_num [robustMarginalCubicWitness])
    (by norm_num [robustMarginalCubicWitness])
    robustMarginalCubicWitness_step

/-- Asymptotic freedom: the marginal coupling tends to `0` in the UV
(`gₙ → 0`), since `1/gₙ ≥ 1/g₀ + βn → ∞`. -/
theorem marginal_coupling_tendsto_zero (g : ℕ → ℝ) {β : ℝ}
    (hβ : 0 < β)
    (hAF : ∀ n : ℕ, 1 / g 0 + β * (n : ℝ) ≤ 1 / g n) :
    Filter.Tendsto g Filter.atTop (nhds 0) := by
  have hinv : Filter.Tendsto (fun n => 1 / g n) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono hAF
    apply Filter.tendsto_atTop_add_const_left
    exact Filter.Tendsto.const_mul_atTop hβ tendsto_natCast_atTop_atTop
  have heq : (fun n => (1 / g n)⁻¹) = g := by funext n; rw [one_div, inv_inv]
  rw [← heq]
  exact hinv.inv_tendsto_atTop

/-- Sanity corollary for the witness: `1 / (k + 4)` tends to zero. -/
theorem robustMarginalCubicWitness_tendsto_zero :
    Filter.Tendsto robustMarginalCubicWitness Filter.atTop (nhds 0) := by
  exact marginal_coupling_tendsto_zero robustMarginalCubicWitness (β := (1 : ℝ) / 2)
    (by norm_num) (fun n => (robustMarginalCubicWitness_invariant n).2.2)

/-- The concrete robust cubic-error witness has a summable `κ`-power tail for
every real `κ > 1`. -/
theorem robustMarginalCubicWitness_rpow_summable {kappa : ℝ} (hkappa : 1 < kappa) :
    Summable (fun k => robustMarginalCubicWitness k ^ kappa) := by
  exact robust_marginal_cubic_error_rpow_summable robustMarginalCubicWitness
    (beta := 1) (C := 1) (by norm_num) (by norm_num)
    (by norm_num [robustMarginalCubicWitness])
    (by norm_num [robustMarginalCubicWitness])
    (by norm_num [robustMarginalCubicWitness])
    robustMarginalCubicWitness_step hkappa

/-- **Marginal-coupling scale-series summability, from the RG recursion.**
The 4D-marginal coupling recursion `g_{k+1} = g_k(1 − β g_k)` (the
asymptotically-free / logistic step, `β·g_k < 1`) gives a summable remainder
series `∑ₙ gₙ^{κ₀}` for `κ₀ > 1`, **without** any geometric-decay assumption
on the coupling.  Composes `inv_coupling_linear_growth` (asymptotic freedom)
with `marginal_coupling_pow_summable`. -/
theorem marginal_coupling_pow_summable_of_recursion (g : ℕ → ℝ) {β κ₀ : ℝ}
    (hβ : 0 < β) (hpos : ∀ k, 0 < g k) (hsmall : ∀ k, β * g k < 1)
    (hrec : ∀ k, g (k + 1) = g k * (1 - β * g k)) (hκ : 1 < κ₀) :
    Summable (fun n => g n ^ κ₀) :=
  marginal_coupling_pow_summable g hβ hpos
    (inv_coupling_linear_growth g hβ.le hpos hsmall hrec) hκ

/-- **Marginal-coupling remainder scale-sum bound** (the honest YM analogue of
the geometric coupling bridge).  Given the renormalization-remainder activity
bound `|R_{t,k}| ≤ A·e^{−c₀t}·g_k^{κ₀}` (the carried Bałaban YM activity input)
and the summability of `g_k^{κ₀}` over scales (`marginal_coupling_pow_summable`,
the marginal coupling — NOT geometric), the scale-summed remainder at distance
`t` decays as `e^{−c₀t}` with a **finite, scale-summed** constant:
`∑ₖ |R_{t,k}| ≤ A·e^{−c₀t}·(∑ₖ g_k^{κ₀})`.  So the UV remainder still gives
the spatial gap factor `e^{−c₀t}`, with the scale series contributing only a
bounded constant — discharging the coupling side for the marginal YM flow
without any false geometric-decay assumption. -/
theorem marginal_coupling_remainder_tsum_le (g : ℕ → ℝ) (R : ℕ → ℕ → ℝ)
    {A c0 κ₀ : ℝ} (_hg : ∀ k, 0 ≤ g k) (hsum : Summable (fun k => g k ^ κ₀))
    (hpoly : ∀ t k, |R t k| ≤ A * Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀) (t : ℕ) :
    ∑' k, |R t k| ≤ A * Real.exp (-(c0 * (t : ℝ))) * ∑' k, g k ^ κ₀ := by
  have hRHSsum : Summable (fun k => A * Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀) :=
    hsum.mul_left _
  have hLHSsum : Summable (fun k => |R t k|) :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => hpoly t k) hRHSsum
  calc ∑' k, |R t k|
      ≤ ∑' k, A * Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀ :=
        Summable.tsum_le_tsum (fun k => hpoly t k) hLHSsum hRHSsum
    _ = A * Real.exp (-(c0 * (t : ℝ))) * ∑' k, g k ^ κ₀ := tsum_mul_left

/-- **Scale-summed marginal remainder directly from the marginal recursion.**
This is the theorem-shaped discharge of the former external summability premise
of `marginal_coupling_remainder_tsum_le`: callers now provide the source-level
marginal RG recursion and small-field assumptions, and Lean derives the
summable scale profile before applying the remainder summation bridge. -/
theorem marginal_coupling_remainder_tsum_le_of_recursion (g : ℕ → ℝ)
    (R : ℕ → ℕ → ℝ) {A c0 β κ₀ : ℝ}
    (hβ : 0 < β) (hpos : ∀ k, 0 < g k) (hsmall : ∀ k, β * g k < 1)
    (hrec : ∀ k, g (k + 1) = g k * (1 - β * g k)) (hκ : 1 < κ₀)
    (hpoly : ∀ t k, |R t k| ≤ A * Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀)
    (t : ℕ) :
    ∑' k, |R t k| ≤ A * Real.exp (-(c0 * (t : ℝ))) * ∑' k, g k ^ κ₀ :=
  marginal_coupling_remainder_tsum_le g R (fun k => (hpos k).le)
    (marginal_coupling_pow_summable_of_recursion g hβ hpos hsmall hrec hκ)
    hpoly t

end YangMills.RG
