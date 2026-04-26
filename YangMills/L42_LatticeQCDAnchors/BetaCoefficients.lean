/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson, Cowork agent (Claude)
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic

/-!
# `L42_LatticeQCDAnchors`: Concrete QCD beta-function coefficients

This module provides **concrete numerical anchors** for the QCD
running-coupling beta function, packaged as Lean definitions and
computed values for SU(2) and SU(3).

These are the foundational coefficients that govern asymptotic
freedom and dimensional transmutation:

  * **One-loop**: `β₀ = (11/3) · N_c` (no fermions; pure Yang-Mills).
  * **Two-loop**: `β₁ = (34/3) · N_c²`.

The coupling `g(μ)` runs according to

  `μ · dg/dμ = -β(g) = -(β₀ · g³ + β₁ · g⁵ + ...)` (MS-bar scheme),

so a positive `β₀` guarantees asymptotic freedom: as `μ → ∞`,
`g(μ) → 0` logarithmically.

Inverting the running gives **dimensional transmutation**:

  `Λ_QCD = μ · exp(-1/(2 · β₀ · g²(μ)))`,

i.e., a single dimensional scale `Λ_QCD` emerges from a dimensionless
coupling. This is the physics origin of the mass gap.

## Strategy

The coefficients are entered as Lean `def`s with `theorem`-form
verifications at SU(2) and SU(3). The theorems are computational
(`norm_num`) sanity checks, not deep results.

## Status

This file is **single-file content** for L42_LatticeQCDAnchors.
It does not yet implement the full RG-running flow (which would
require ODE infrastructure beyond elementary `norm_num`).

**Status (2026-04-25)**: produced in the workspace, not yet built
with `lake build`. The proofs are `norm_num` and `unfold` only.
-/

namespace LatticeQCD

/-! ## §1. Beta function coefficients -/

/-- **One-loop beta function coefficient** (pure Yang-Mills, no fermions):

      `β₀(N_c) = (11/3) · N_c`.

    This is the foundational coefficient governing asymptotic freedom.
    For QCD at low energies (only gluons, ~ 3 active quark flavours
    not yet relevant), this expression captures the dominant behavior. -/
def betaZero (N_c : ℕ) : ℝ := 11/3 * (N_c : ℝ)

/-- **Two-loop beta function coefficient** (pure Yang-Mills):

      `β₁(N_c) = (34/3) · N_c²`. -/
def betaOne (N_c : ℕ) : ℝ := 34/3 * (N_c : ℝ)^2

/-! ## §2. Concrete values at SU(2) -/

/-- **SU(2) one-loop**: `β₀ = 22/3 ≈ 7.333`. -/
theorem betaZero_SU2 : betaZero 2 = 22/3 := by
  unfold betaZero
  norm_num

/-- **SU(2) two-loop**: `β₁ = 136/3 ≈ 45.333`. -/
theorem betaOne_SU2 : betaOne 2 = 136/3 := by
  unfold betaOne
  norm_num

/-! ## §3. Concrete values at SU(3) (= QCD) -/

/-- **SU(3) one-loop (QCD)**: `β₀ = 11`. This is the foundational
    QCD coefficient. -/
theorem betaZero_SU3 : betaZero 3 = 11 := by
  unfold betaZero
  norm_num

/-- **SU(3) two-loop (QCD)**: `β₁ = 102`. -/
theorem betaOne_SU3 : betaOne 3 = 102 := by
  unfold betaOne
  norm_num

/-! ## §4. Asymptotic freedom: `β₀ > 0` for `N_c ≥ 1` -/

/-- **Asymptotic freedom condition**: for any `N_c ≥ 1`, `β₀ > 0`.

    This is the **structural reason** the coupling decreases at high
    energy (UV-asymptotic freedom). The 't Hooft and Politzer-Wilczek
    discovery of asymptotic freedom rests on this inequality. -/
theorem betaZero_pos {N_c : ℕ} (hN : 1 ≤ N_c) : 0 < betaZero N_c := by
  unfold betaZero
  have h_N_pos : (0 : ℝ) < (N_c : ℝ) := by exact_mod_cast hN
  positivity

/-! ## §5. Two-loop strict positivity -/

/-- **Two-loop coefficient positivity**: for any `N_c ≥ 1`, `β₁ > 0`. -/
theorem betaOne_pos {N_c : ℕ} (hN : 1 ≤ N_c) : 0 < betaOne N_c := by
  unfold betaOne
  have h_N_pos : (0 : ℝ) < (N_c : ℝ) := by exact_mod_cast hN
  positivity

/-! ## §6. Ratio `β₁ / β₀²` (scheme-independent) -/

/-- **Scheme-independent ratio** `β₁ / β₀²`.

    Unlike individual `β₀`, `β₁` (which depend on the regularisation
    scheme), the ratio `β₁ / β₀²` is scheme-independent and captures a
    fundamental aspect of the theory. -/
def betaOneOverZeroSq (N_c : ℕ) : ℝ :=
  betaOne N_c / (betaZero N_c)^2

/-- **Computed ratio at SU(2)**: `β₁ / β₀² = (136/3) / (22/3)² = (136/3) · (9/484) = 408/484 = 102/121`. -/
theorem betaOneOverZeroSq_SU2 : betaOneOverZeroSq 2 = 102/121 := by
  unfold betaOneOverZeroSq betaOne betaZero
  norm_num

/-- **Computed ratio at SU(3)**: `β₁ / β₀² = 102 / 121 ≈ 0.843`. -/
theorem betaOneOverZeroSq_SU3 : betaOneOverZeroSq 3 = 102/121 := by
  unfold betaOneOverZeroSq betaOne betaZero
  norm_num

/-! ## §7. Universal observation -/

/-- **Universal scheme-independent ratio**: `β₁ / β₀² = 102/121` for
    any `N_c ≥ 1` in pure Yang-Mills.

    This is a direct consequence of `β₀ = (11/3)N_c` and
    `β₁ = (34/3)N_c²` having the same `N_c`-scaling structure: the
    `N_c`'s cancel in the ratio. -/
theorem betaOneOverZeroSq_universal {N_c : ℕ} (hN : 1 ≤ N_c) :
    betaOneOverZeroSq N_c = 102/121 := by
  unfold betaOneOverZeroSq betaOne betaZero
  have h_N_pos : (0 : ℝ) < (N_c : ℝ) := by exact_mod_cast hN
  have h_N_ne : (N_c : ℝ) ≠ 0 := ne_of_gt h_N_pos
  field_simp
  ring

#print axioms betaOneOverZeroSq_universal

/-! ## §8. Lambda_QCD scale (dimensional transmutation) -/

/-- **Lambda_QCD scale** at one-loop: `Λ_QCD(μ, g(μ)) = μ · exp(-1/(2 · β₀ · g²(μ)))`.

    This expression makes manifest the **dimensional transmutation**:
    a single mass scale emerges from the dimensionless coupling. -/
noncomputable def lambdaQCD (N_c : ℕ) (μ g_sq : ℝ) : ℝ :=
  μ * Real.exp (-1 / (2 * betaZero N_c * g_sq))

/-- **Lambda_QCD positivity**: for `N_c ≥ 1`, `μ > 0`, `g² > 0`,
    `Λ_QCD > 0`. -/
theorem lambdaQCD_pos {N_c : ℕ} (hN : 1 ≤ N_c) {μ g_sq : ℝ}
    (hμ : 0 < μ) (hg : 0 < g_sq) :
    0 < lambdaQCD N_c μ g_sq := by
  unfold lambdaQCD
  exact mul_pos hμ (Real.exp_pos _)

#print axioms lambdaQCD_pos

end LatticeQCD
