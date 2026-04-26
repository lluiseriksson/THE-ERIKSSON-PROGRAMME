/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson, Cowork agent (Claude)
-/
import YangMills.L42_LatticeQCDAnchors.BetaCoefficients

/-!
# `L44_LargeNLimit.HooftCoupling`: The 't Hooft coupling

This module formalises the **'t Hooft coupling** of large-N gauge
theory:

  `λ = g² · N_c`,

held fixed in the **large-N limit** `N_c → ∞`. This is the foundational
object of the **'t Hooft 1/N expansion** (1974), which organises pure
Yang-Mills perturbation theory around the planar (genus-0) diagrams.

## Mathematical content

The 't Hooft expansion provides:

* **Leading order (planar)**: glueball masses decouple from `1/N`
  corrections; the theory is exactly solvable in 2D and tractable in
  4D up to the planar resummation.
* **Subleading 1/N corrections**: systematic expansion in `1/N²`.
* **Asymptotic freedom in `λ`**: at fixed 't Hooft coupling, the
  beta function is `μ · dλ/dμ = -β₀ · λ²` (one-loop), where
  `β₀ = (11/3) · N_c` becomes proportional to `N_c`. Dividing through
  by `N_c`: `μ · d(λ/N_c)/dμ = -(11/3) · (λ/N_c)² · N_c`, i.e., the
  reduced beta function in `λ` is `-(11/3) · λ²` independent of `N_c`.

This module defines `λ` and proves the basic algebraic properties.

## Strategy

The 't Hooft coupling is encoded as a `def`. The dimensional structure
(λ is dimensionless) and positivity are proved.

## Status

This file is structural physics scaffolding. The substantive
content of large-N expansions (planar dominance, 1/N corrections)
requires deeper Mathlib infrastructure for diagrammatic / Feynman
rules.

**Status (2026-04-25)**: produced in workspace, not yet built with
`lake build`. Proofs are direct algebraic manipulations.
-/

namespace L44_LargeNLimit

open LatticeQCD

/-! ## §1. The 't Hooft coupling -/

/-- **'t Hooft coupling** `λ = g² · N_c`.

    This is the fundamental dimensionless quantity organising the
    1/N expansion. -/
noncomputable def hooftCoupling (N_c : ℕ) (g_sq : ℝ) : ℝ :=
  g_sq * (N_c : ℝ)

/-! ## §2. Positivity -/

/-- **Positivity of the 't Hooft coupling**: for `g² > 0` and
    `N_c ≥ 1`, the 't Hooft coupling is positive. -/
theorem hooftCoupling_pos {N_c : ℕ} (hN : 1 ≤ N_c) {g_sq : ℝ}
    (hg : 0 < g_sq) :
    0 < hooftCoupling N_c g_sq := by
  unfold hooftCoupling
  have h_N_pos : (0 : ℝ) < (N_c : ℝ) := by exact_mod_cast hN
  exact mul_pos hg h_N_pos

#print axioms hooftCoupling_pos

/-! ## §3. The reduced beta function -/

/-- **Reduced one-loop beta function** in the 't Hooft coupling:

      `β_λ(λ) = -(11/3) · λ²`,

    independent of `N_c` (the `N_c`-dependence is absorbed into `λ`).

    This is the **structural reason** the 't Hooft expansion is so
    powerful: at fixed `λ`, the running is `N_c`-independent at one
    loop. -/
noncomputable def hooftBetaReduced (lam : ℝ) : ℝ := -(11/3) * lam^2

/-- **Reduced beta function is non-positive**: `β_λ(λ) ≤ 0` for any
    real `λ` (positive or negative).

    Equivalent to **`λ` decreasing under RG flow** at one loop:
    asymptotic freedom in the 't Hooft coupling. -/
theorem hooftBetaReduced_nonpos (lam : ℝ) : hooftBetaReduced lam ≤ 0 := by
  unfold hooftBetaReduced
  have h_sq : 0 ≤ lam^2 := sq_nonneg lam
  linarith

#print axioms hooftBetaReduced_nonpos

/-- **Reduced beta function strict negative**: for `λ ≠ 0`, the
    reduced beta function is strictly negative. -/
theorem hooftBetaReduced_neg_of_ne {lam : ℝ} (hlam : lam ≠ 0) :
    hooftBetaReduced lam < 0 := by
  unfold hooftBetaReduced
  have h_sq_pos : 0 < lam^2 := by positivity
  linarith

#print axioms hooftBetaReduced_neg_of_ne

/-! ## §4. Connection to original beta function via `N_c` -/

/-- **Bridge**: the original one-loop beta function for `g²` and the
    reduced one for `λ = g²·N_c` are related by

      `β_g² = β_λ / N_c`.

    This packages the **`N_c`-rescaling** that produces the reduced
    beta function. -/
theorem hoof_betaReduced_eq_betaZero_lam_sq {N_c : ℕ} (hN : 1 ≤ N_c)
    (g_sq : ℝ) :
    hooftBetaReduced (hooftCoupling N_c g_sq) =
    -(betaZero N_c) * (hooftCoupling N_c g_sq)^2 / (N_c : ℝ) := by
  unfold hooftBetaReduced betaZero hooftCoupling
  have h_N_pos : (0 : ℝ) < (N_c : ℝ) := by exact_mod_cast hN
  have h_N_ne : (N_c : ℝ) ≠ 0 := ne_of_gt h_N_pos
  field_simp
  ring

#print axioms hoof_betaReduced_eq_betaZero_lam_sq

/-! ## §5. Numerical instances -/

/-- **At SU(2)**: `λ = 2 · g²`. -/
theorem hooftCoupling_SU2 (g_sq : ℝ) : hooftCoupling 2 g_sq = 2 * g_sq := by
  unfold hooftCoupling
  ring

/-- **At SU(3) (= QCD)**: `λ = 3 · g²`. -/
theorem hooftCoupling_SU3 (g_sq : ℝ) : hooftCoupling 3 g_sq = 3 * g_sq := by
  unfold hooftCoupling
  ring

#print axioms hooftCoupling_SU3

/-! ## §6. Large-N limit -/

/-- **Large-N limit interpretation**: in the limit `N_c → ∞` with
    `λ = g²·N_c` held fixed, the 't Hooft coupling provides the
    **right organising parameter** for perturbation theory.

    This is encoded conceptually as the assertion that `hooftCoupling`
    is the natural argument; substantive treatment of the `N_c → ∞`
    limit requires further infrastructure (e.g., asymptotic
    expansions, planar diagrammatics).

    Encoded as a `theorem` whose body is `trivial` — conceptual
    signpost, not substantive claim. -/
theorem largeN_limit_signpost : True := trivial

end L44_LargeNLimit
