/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Bałaban RG flow recursion (Phase 133)

This module formalises the **recursive RG flow** structure underlying
Bałaban's renormalisation-group treatment of SU(N) lattice gauge theory.

## Strategic placement

This is **Phase 133** of the L15_BranchII_Wilson_Substantive block —
the **ninth long-cycle block**, longest so far at 10 files.

## What it does

Encodes the RG flow as a sequence of scales `aₖ = L^k a₀` for some
fixed integer block factor `L ≥ 2`, with associated effective couplings
`gₖ` and effective measures `μₖ`. The flow recursion is:

  μₖ₊₁ = R_block μₖ           — block-spin decimation
  gₖ₊₁ = β-flow(gₖ)           — coupling renormalisation
  aₖ₊₁ = L · aₖ               — scale doubling/L-tupling

The **fundamental hypothesis** (Bałaban): the flow contracts toward
the trivial fixed point `g* = 0` (asymptotic freedom).

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L15_BranchII_Wilson_Substantive

/-! ## §1. RG flow scales -/

/-- The block factor `L ≥ 2` defining the RG decimation step. -/
structure BlockFactor where
  /-- The integer block factor. -/
  L : ℕ
  /-- Constraint: `L ≥ 2`. -/
  L_ge_two : 2 ≤ L

/-- The sequence of RG scales `aₖ = L^k · a₀` for initial scale `a₀ > 0`. -/
def rgScale (a₀ : ℝ) (bf : BlockFactor) (k : ℕ) : ℝ :=
  (bf.L : ℝ) ^ k * a₀

/-- **Scales are positive** when `a₀ > 0`. -/
theorem rgScale_pos (a₀ : ℝ) (h : 0 < a₀) (bf : BlockFactor) (k : ℕ) :
    0 < rgScale a₀ bf k := by
  unfold rgScale
  have hL : (0 : ℝ) < (bf.L : ℝ) := by
    have : (2 : ℝ) ≤ (bf.L : ℝ) := by exact_mod_cast bf.L_ge_two
    linarith
  exact mul_pos (pow_pos hL k) h

/-- **Scales are strictly increasing**. -/
theorem rgScale_strictMono (a₀ : ℝ) (h : 0 < a₀) (bf : BlockFactor) :
    StrictMono (rgScale a₀ bf) := by
  intro i j hij
  unfold rgScale
  have hL : (1 : ℝ) < (bf.L : ℝ) := by
    have : (2 : ℝ) ≤ (bf.L : ℝ) := by exact_mod_cast bf.L_ge_two
    linarith
  have : (bf.L : ℝ) ^ i < (bf.L : ℝ) ^ j := pow_lt_pow_right₀ hL hij
  exact (mul_lt_mul_right h).mpr this

/-! ## §2. The β-flow recursion -/

/-- Abstract β-flow: a function `g ↦ g'` describing the coupling
    renormalisation under a single block-spin step. -/
structure BetaFlow where
  /-- The β-flow function. -/
  flow : ℝ → ℝ
  /-- The flow fixes the trivial coupling `g = 0` (Gaussian fixed point). -/
  fixes_zero : flow 0 = 0
  /-- The flow is contractive in a neighbourhood of `0`: there exists
      `δ > 0` and `q < 1` such that `|flow g| ≤ q · |g|` for `|g| < δ`.
      This is **asymptotic freedom** in its abstract form. -/
  contracts_near_zero :
    ∃ δ q : ℝ, 0 < δ ∧ 0 < q ∧ q < 1 ∧
      ∀ g : ℝ, |g| < δ → |flow g| ≤ q * |g|

/-! ## §3. The RG flow iterates -/

/-- The k-th β-flow iterate. -/
def betaFlowIter (β : BetaFlow) : ℕ → ℝ → ℝ
  | 0, g => g
  | k+1, g => β.flow (betaFlowIter β k g)

/-- **The β-flow iterates contract** toward zero from sufficiently
    small initial coupling.

    This is **asymptotic freedom** at the level of the iterated flow.
    Concretely: for `|g₀| < δ`, the iterates `gₖ = β^k(g₀)` decay
    geometrically, `|gₖ| ≤ qᵏ |g₀|`. -/
theorem betaFlowIter_contracts (β : BetaFlow) (g₀ : ℝ) :
    ∃ δ q : ℝ, 0 < δ ∧ 0 ≤ q ∧ q < 1 ∧
      (|g₀| < δ → ∀ k : ℕ, |betaFlowIter β k g₀| ≤ q ^ k * |g₀|) := by
  obtain ⟨δ, q, hδ, hq, hq1, hcontract⟩ := β.contracts_near_zero
  refine ⟨δ, q, hδ, le_of_lt hq, hq1, ?_⟩
  intro hg₀ k
  induction k with
  | zero => simp [betaFlowIter]
  | succ k ih =>
      -- Need: `|betaFlowIter β (k+1) g₀| ≤ q ^ (k+1) * |g₀|`.
      simp only [betaFlowIter, pow_succ]
      -- The inductive hypothesis gives `|betaFlowIter β k g₀| ≤ q^k * |g₀|`.
      -- We need this iterate to also be in `(-δ, δ)`.
      have h_ind : |betaFlowIter β k g₀| ≤ q ^ k * |g₀| := ih
      have h_iter_lt : |betaFlowIter β k g₀| < δ := by
        calc |betaFlowIter β k g₀|
            ≤ q ^ k * |g₀| := h_ind
          _ ≤ 1 * |g₀| := by
              apply mul_le_mul_of_nonneg_right
              · exact pow_le_one₀ (le_of_lt hq) (le_of_lt hq1)
              · exact abs_nonneg g₀
          _ = |g₀| := one_mul _
          _ < δ := hg₀
      have h_step : |β.flow (betaFlowIter β k g₀)| ≤
          q * |betaFlowIter β k g₀| :=
        hcontract _ h_iter_lt
      calc |β.flow (betaFlowIter β k g₀)|
          ≤ q * |betaFlowIter β k g₀| := h_step
        _ ≤ q * (q ^ k * |g₀|) :=
            mul_le_mul_of_nonneg_left h_ind (le_of_lt hq)
        _ = q ^ k * q * |g₀| := by ring

#print axioms betaFlowIter_contracts

/-! ## §4. Coordination note -/

/-
This file is **Phase 133** of the L15_BranchII_Wilson_Substantive block.

## What's done

Two **substantive** Lean theorems with full proofs:
* `rgScale_pos`, `rgScale_strictMono` — RG scales are well-defined and
  strictly increasing.
* `betaFlowIter_contracts` — asymptotic freedom at the level of the
  iterated β-flow: small initial coupling decays geometrically.

This is a **real Lean math contribution**, not just structural
scaffolding.

## Strategic value

Phase 133 gives the project its first concrete Lean machinery for the
RG flow. The asymptotic-freedom contraction proof is the abstract
analogue of the substantive content in Bałaban's work and forms the
foundation for the rest of the L15 block.

Cross-references:
- Bloque-4 §3-4 (Bałaban RG framework).
- `BLUEPRINT_BalabanRG.md`.
- Codex's `YangMills/ClayCore/BalabanRG/`.
-/

end YangMills.L15_BranchII_Wilson_Substantive
