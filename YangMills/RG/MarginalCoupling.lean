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

* **`marginal_coupling_pow_summable`** — from the asymptotic-freedom lower
  bound `1/g₀ + β·n ≤ 1/gₙ` (the conclusion of `inv_coupling_linear_growth`),
  `β > 0`, and `κ₀ > 1`, the series `∑ₙ gₙ^{κ₀}` converges.  Proof: `gₙ ≤
  1/(c(n+1))`, then comparison with the convergent `p`-series `∑ n^{−κ₀}`.
* **`marginal_coupling_tendsto_zero`** — asymptotic freedom proper: `gₙ → 0`.
* **`marginal_coupling_pow_summable_of_recursion`** — the same summability
  directly from the marginal recursion `g_{k+1} = g_k(1 − β g_k)`.

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
  have hb : (0 : ℝ) < 1 / g 0 + β * (n : ℝ) := by positivity
  have h1 : g n * (1 / g 0 + β * (n : ℝ)) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left (hAF n) (hpos n).le
    rwa [mul_one_div, div_self (hpos n).ne'] at this
  have hgle : g n ≤ 1 / (1 / g 0 + β * (n : ℝ)) := (le_div_iff₀ hb).mpr h1
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
    {A c0 κ₀ : ℝ} (hg : ∀ k, 0 ≤ g k) (hsum : Summable (fun k => g k ^ κ₀))
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

end YangMills.RG
