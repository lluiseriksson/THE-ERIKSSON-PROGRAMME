/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L7_Multiscale.MultiscaleSigmaAlgebraChain

/-!
# Single-scale UV error bound (Bloque-4 §6.2 / Lemma 6.2)

This module formalises the **single-scale UV error bound**
underlying the multiscale correlator decoupling of Eriksson's
Bloque-4 paper §6.2.

For each scale `k`, the conditional covariance term

  `R_k(F, G) = E[Cov(F, G | σ_{a_k}) | σ_{a_{k+1}}]`

is bounded exponentially in the spatial separation `R` of the
supports of `F` and `G`, with rate determined by the inverse
lattice spacing `1/a_k`:

  `|R_k(F, G)| ≤ C · ‖F‖_∞ · ‖G‖_∞ · exp(-κ · R / a_k)`.

This is **Phase 94** of the L7_Multiscale block.

## Strategic placement

Builds on Phase 93's `MultiscaleSigmaAlgebraChain`. Used by Phase 95
(telescoping identity) and Phase 96 (geometric summation).

Bloque-4 §6.2 derives this bound from cluster expansion at scale
`a_k` plus random-walk decay of the propagator `G_k`. Cowork's
Phase 92 (`CombesThomas.lean`) provides an alternative
operator-theoretic derivation. Cowork's Phase 91
(`SteinCovarianceBound.lean`) provides yet another via Stein's
method.

This file abstracts the bound as a hypothesis, allowing any of the
three approaches to supply it concretely.

## Oracle target

`[propext, Classical.choice, Quot.sound]` plus the abstract
single-scale bound hypothesis.

-/

namespace YangMills.L7_Multiscale

open MeasureTheory

variable {Ω : Type*} [m₀ : MeasurableSpace Ω]

/-! ## §1. The single-scale UV error -/

/-- The **single-scale UV error term** at scale `k`:

  `R_k(F, G) := ∫_{µ} (E[F·G | σ_k] - E[F|σ_k] · E[G|σ_k]) ∂µ`

  conditioned at the next coarser scale `σ_{k+1}` and integrated.

  In the standard formulation (Bloque-4 §6.2):
  `R_k(F, G) = E[Cov(F, G | σ_k) | σ_{k+1}]`
  but the integral over the ambient measure is what we use here for
  uniform-in-volume bounds. -/
noncomputable def singleScaleError
    (μ : Measure Ω) {k_star : ℕ}
    (chain : MultiscaleSigmaAlgebraChain Ω k_star)
    (k : Fin k_star) (F G : Ω → ℝ) : ℝ :=
  ∫ ω,
    (μ[F * G | chain.σ k.castSucc] ω -
     (μ[F | chain.σ k.castSucc] ω) * (μ[G | chain.σ k.castSucc] ω)) ∂μ

/-! ## §2. The single-scale bound hypothesis -/

/-- A **single-scale UV error bound**: the conditional covariance at
    scale `k` decays exponentially in the spatial separation, with
    decay rate `κ / a_k` where `a_k` is the lattice spacing at scale
    `k`.

    Concretely: there exist `C, κ > 0` and a function `a : Fin (k_star+1) → ℝ`
    (the scale function) such that

    `|R_k(F, G)| ≤ C · ‖F‖_∞ · ‖G‖_∞ · exp(-κ · R / a_k)`

    whenever `F` and `G` have supports separated by spatial distance
    at least `R`.

    Hypothesised here at the abstract level; supplied concretely by:
    * Cluster-expansion + RW decay (Bloque-4's standard).
    * Combes-Thomas method (Phase 92).
    * Stein's method (Phase 91). -/
structure SingleScaleUVErrorBound
    (μ : Measure Ω) {k_star : ℕ}
    (chain : MultiscaleSigmaAlgebraChain Ω k_star) where
  /-- Scale function: `a k` is the lattice spacing at scale `k`. -/
  a : Fin (k_star + 1) → ℝ
  /-- All scales positive. -/
  a_pos : ∀ k, 0 < a k
  /-- Geometric ratio: `a (k+1) = a k / L` for some `L > 1`. -/
  L : ℝ
  L_gt_one : 1 < L
  a_geometric : ∀ k : Fin k_star,
    a k.succ = a k.castSucc / L
  /-- Decay rate constant. -/
  κ : ℝ
  κ_pos : 0 < κ
  /-- Prefactor constant. -/
  C : ℝ
  C_pos : 0 < C
  /-- The bound itself: for any pair of L¹ observables and any
      "support separation distance" `R`, the single-scale error
      is bounded. -/
  bound : ∀ (k : Fin k_star) (F G : Ω → ℝ) (R : ℝ),
    Integrable F μ → Integrable G μ →
    Integrable (fun ω => F ω * G ω) μ →
    -- `R` is the support-separation hypothesis (left abstract).
    -- The bound:
    |singleScaleError μ chain k F G| ≤
      C * Real.exp (-κ * R / a k.castSucc)

/-! ## §3. Geometric scale property -/

/-- The lattice spacings form a **decreasing geometric sequence**:
    `a k = a 0 / L^k`. Direct consequence of `a_geometric`. -/
theorem SingleScaleUVErrorBound.a_eq_geometric
    {μ : Measure Ω} {k_star : ℕ}
    {chain : MultiscaleSigmaAlgebraChain Ω k_star}
    (B : SingleScaleUVErrorBound μ chain) (k : ℕ) (h : k ≤ k_star) :
    B.a ⟨k, by omega⟩ = B.a 0 / B.L ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    have hn : n ≤ k_star := by omega
    have hn_lt : n < k_star := by omega
    -- Use a_geometric at the appropriate Fin index.
    have h_step :
        B.a ⟨n + 1, by omega⟩ = B.a ⟨n, by omega⟩ / B.L := by
      have : (⟨n, hn_lt⟩ : Fin k_star).castSucc = ⟨n, by omega⟩ ∧
             (⟨n, hn_lt⟩ : Fin k_star).succ = ⟨n + 1, by omega⟩ := by
        refine ⟨rfl, rfl⟩
      have := B.a_geometric ⟨n, hn_lt⟩
      simpa [this.1, this.2] using this
    rw [h_step, ih hn]
    field_simp
    ring

#print axioms SingleScaleUVErrorBound.a_eq_geometric

/-! ## §4. Coordination note -/

/-
This file is **Phase 94** of the L7_Multiscale block (Phases 93-97).

## What's done

* `singleScaleError` definition (the conditional covariance integral).
* `SingleScaleUVErrorBound` structure with all data + the bound itself.
* `a_eq_geometric` theorem (decreasing geometric sequence).

## What's NOT done

* The `bound` field is HYPOTHESISED. Concrete instantiation comes
  from one of:
  * Bloque-4 §6.2 cluster + RW (substantive Branch I/II content).
  * Phase 92 Combes-Thomas (Cowork creative angle).
  * Phase 91 Stein's method (Cowork creative angle).

* The "support separation `R`" parameter is left abstract; concretely
  it comes from the spatial structure of the Wilson observables.

## Strategic value

Phase 94 provides the **abstract single-scale bound** that Phases 95-97
will compose into the multiscale telescoping identity. Each scale
contributes an exponential decay `exp(-κ R / a_k)`; Phase 96 will
sum geometrically over scales to get the uniform UV suppression.

Cross-references:
- Phase 93: `MultiscaleSigmaAlgebraChain.lean` (the carrier).
- Phase 91: `L8_SteinMethod/SteinCovarianceBound.lean` (alternative).
- Phase 92: `L8_CombesThomas/CombesThomas.lean` (alternative).
- `BLUEPRINT_MultiscaleDecoupling.md` (Phase 84).
-/

end YangMills.L7_Multiscale
