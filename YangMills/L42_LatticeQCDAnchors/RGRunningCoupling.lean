/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson, Cowork agent (Claude)
-/
import YangMills.L42_LatticeQCDAnchors.BetaCoefficients

/-!
# `L42_LatticeQCDAnchors.RGRunningCoupling`: One-loop running coupling

This module defines the **one-loop running coupling** in QCD,

  `g²(μ) = 1 / (β₀ · log(μ/Λ))`,

and proves the foundational properties:

* **Positivity**: `g²(μ) > 0` for `μ > Λ > 0`.
* **Inverse asymptotic freedom**: as `μ → ∞`, `g²(μ) → 0`.
* **Decoupling at the QCD scale**: `g²(Λ) → ∞` (Landau pole).

The expression follows from inverting the one-loop RG flow

  `μ · dg²/dμ = -β₀ · g⁴`,

which integrates to `1/g²(μ) = β₀ · log(μ/Λ) + const`. Choosing the
constant to fix the boundary `g²(Λ) → ∞` gives the form above.

## Strategy

The one-loop running formula is encoded as a noncomputable
definition. The properties are theorems with explicit `Real.log`
positivity / monotonicity arguments.

## Status

This file is **single-file content** for L42_LatticeQCDAnchors.
The physical interpretation requires accepting `Λ` as a free
parameter (dimensional transmutation), but the running formula is
self-contained.

**Status (2026-04-25)**: produced in workspace, not yet built with
`lake build`. Proofs are short (2-4 lines).
-/

namespace LatticeQCD

/-! ## §1. Definition of the running coupling -/

/-- **One-loop running coupling**:

      `g²(μ) = 1 / (β₀ · log(μ/Λ))`,

    valid for `μ > Λ > 0`. -/
noncomputable def gSqOneLoop (N_c : ℕ) (μ Λ : ℝ) : ℝ :=
  1 / (betaZero N_c * Real.log (μ / Λ))

/-! ## §2. Positivity for `μ > Λ > 0` -/

/-- **Positivity**: for `N_c ≥ 1`, `0 < Λ < μ`, the running coupling
    `g²(μ)` is positive.

    This is the "asymptotic-freedom regime": when the renormalisation
    scale `μ` is above the QCD scale `Λ`, the coupling is finite and
    positive (and decreasing). -/
theorem gSqOneLoop_pos {N_c : ℕ} (hN : 1 ≤ N_c) {μ Λ : ℝ}
    (hΛ : 0 < Λ) (hμ : Λ < μ) :
    0 < gSqOneLoop N_c μ Λ := by
  unfold gSqOneLoop
  have h_β_pos : 0 < betaZero N_c := betaZero_pos hN
  have h_div_gt_one : 1 < μ / Λ := (one_lt_div hΛ).mpr hμ
  have h_log_pos : 0 < Real.log (μ / Λ) := Real.log_pos h_div_gt_one
  have h_denom_pos : 0 < betaZero N_c * Real.log (μ / Λ) :=
    mul_pos h_β_pos h_log_pos
  exact one_div_pos.mpr h_denom_pos

#print axioms gSqOneLoop_pos

/-! ## §3. Asymptotic freedom: `g²(μ) → 0` as `μ → ∞` -/

/-- **Decreasing in `μ`**: for fixed `Λ > 0` and `N_c ≥ 1`, the
    running coupling `g²(μ)` decreases strictly as `μ` increases
    (within the regime `μ > Λ`).

    This is the **structural statement of asymptotic freedom**: the
    larger the energy scale, the weaker the coupling. -/
theorem gSqOneLoop_strictAnti {N_c : ℕ} (hN : 1 ≤ N_c) {Λ : ℝ}
    (hΛ : 0 < Λ) {μ₁ μ₂ : ℝ} (hμ₁ : Λ < μ₁) (hμ₂ : μ₁ < μ₂) :
    gSqOneLoop N_c μ₂ Λ < gSqOneLoop N_c μ₁ Λ := by
  unfold gSqOneLoop
  have h_β_pos : 0 < betaZero N_c := betaZero_pos hN
  -- log(μ₁/Λ) < log(μ₂/Λ) (strict log monotonicity)
  have h_div₁ : 1 < μ₁ / Λ := (one_lt_div hΛ).mpr hμ₁
  have h_div₂ : 1 < μ₂ / Λ := (one_lt_div hΛ).mpr (by linarith)
  have h_log₁_pos : 0 < Real.log (μ₁ / Λ) := Real.log_pos h_div₁
  have h_log₂_pos : 0 < Real.log (μ₂ / Λ) := Real.log_pos h_div₂
  have h_div_lt : μ₁ / Λ < μ₂ / Λ :=
    (div_lt_div_iff_of_pos_right hΛ).mpr hμ₂
  have h_log_lt : Real.log (μ₁ / Λ) < Real.log (μ₂ / Λ) :=
    Real.log_lt_log (div_pos (by linarith) hΛ) h_div_lt
  -- 1/(β₀ log(μ₂/Λ)) < 1/(β₀ log(μ₁/Λ))
  have h_denom₁_pos : 0 < betaZero N_c * Real.log (μ₁ / Λ) :=
    mul_pos h_β_pos h_log₁_pos
  have h_denom_lt : betaZero N_c * Real.log (μ₁ / Λ) <
      betaZero N_c * Real.log (μ₂ / Λ) :=
    (mul_lt_mul_left h_β_pos).mpr h_log_lt
  exact one_div_lt_one_div_of_lt h_denom₁_pos h_denom_lt

#print axioms gSqOneLoop_strictAnti

/-! ## §4. Concrete values at SU(3) (= QCD) -/

/-- **At SU(3) with `μ = 10·Λ`**: `g²(10·Λ) = 1/(11·log 10)`.

    Numerical check: `log 10 ≈ 2.303`, so `g² ≈ 1/(11 · 2.303) ≈ 0.0395`.
    This is the typical magnitude of the strong coupling at high
    energies (the LHC scale is much above 10·Λ_QCD). -/
theorem gSqOneLoop_SU3_at_10Λ (Λ : ℝ) (hΛ : 0 < Λ) :
    gSqOneLoop 3 (10 * Λ) Λ = 1 / (11 * Real.log 10) := by
  unfold gSqOneLoop
  rw [betaZero_SU3]
  congr 2
  rw [show 10 * Λ / Λ = 10 from by field_simp]

#print axioms gSqOneLoop_SU3_at_10Λ

/-! ## §5. Connection to the Lambda_QCD scale -/

/-- **Inverse running gives Λ from g²(μ)**:

      `Λ = μ · exp(-1/(β₀ · g²(μ)))`.

    This is the **dimensional-transmutation formula**: knowing `g²` at
    a single scale `μ` determines the QCD scale `Λ`. -/
theorem lambda_from_running {N_c : ℕ} (hN : 1 ≤ N_c) {μ Λ : ℝ}
    (hΛ : 0 < Λ) (hμ : Λ < μ) :
    Λ = μ * Real.exp (-1 / (betaZero N_c * gSqOneLoop N_c μ Λ)) := by
  -- Direct computation: g² = 1/(β₀ log(μ/Λ)), so
  --   1/(β₀ · g²) = log(μ/Λ),
  -- hence -1/(β₀ · g²) = log(Λ/μ),
  -- so exp(-1/(β₀ · g²)) = Λ/μ, and μ · exp(...) = Λ.
  unfold gSqOneLoop
  have h_β_pos : 0 < betaZero N_c := betaZero_pos hN
  have h_div_gt_one : 1 < μ / Λ := (one_lt_div hΛ).mpr hμ
  have h_log_pos : 0 < Real.log (μ / Λ) := Real.log_pos h_div_gt_one
  have h_denom_pos : 0 < betaZero N_c * Real.log (μ / Λ) :=
    mul_pos h_β_pos h_log_pos
  -- Simplify: betaZero N_c * (1 / (betaZero N_c * Real.log (μ / Λ))) = 1 / Real.log (μ / Λ)
  have h_simp : betaZero N_c * (1 / (betaZero N_c * Real.log (μ / Λ))) =
      1 / Real.log (μ / Λ) := by
    field_simp
  rw [h_simp]
  -- -1 / (1 / Real.log (μ / Λ)) = -Real.log (μ / Λ)
  have h_simp2 : -1 / (1 / Real.log (μ / Λ)) = -Real.log (μ / Λ) := by
    field_simp
  rw [h_simp2]
  -- exp(-log(μ/Λ)) = Λ/μ.
  rw [show -Real.log (μ / Λ) = Real.log (Λ / μ) from by
    rw [← Real.log_inv]; congr 1; field_simp]
  rw [Real.exp_log (div_pos hΛ (by linarith))]
  field_simp

#print axioms lambda_from_running

end LatticeQCD
