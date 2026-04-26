/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson

This file is a **Mathlib-PR-ready draft** of the Law of Total
Covariance, intended for upstream contribution to
`Mathlib/Probability/Moments/Covariance.lean` (or a sibling file).
The current location under `YangMills/MathlibUpstream/` is a staging
ground; if the proofs verify, the file is to be ported to Mathlib
and removed from the project.
-/
import Mathlib

/-!
# Law of Total Covariance

This module establishes the **Law of Total Covariance** (LTC):

  cov(X, Y) = 𝔼[cov(X, Y | m)] + cov(𝔼[X | m], 𝔼[Y | m]),

where `m` is a sub-σ-algebra of the ambient measurable structure.

## Why this matters for Yang–Mills

The LTC is the analytic foundation of the **multiscale correlator
decoupling** in Eriksson's Bloque-4 paper (Proposition 6.1, the
"telescoping identity"):

  Cov_µ_η(F, G) = Cov_µ_a*(F̃, G̃) + Σ_k R_k(F, G)

where each R_k is a conditional covariance at scale a_k,
F̃ = 𝔼[F | σ_a*], etc. The LTC, applied iteratively along the
σ-algebra chain σ_{a_0} ⊃ σ_{a_1} ⊃ ⋯ ⊃ σ_{a_*}, gives the
telescoping decomposition that drives the multiscale mass-gap
argument.

Mathlib already has `ProbabilityTheory.covariance` and
`MeasureTheory.condExp`; this file is the missing capstone
combining them.

## Definitions

* `condCovariance m μ X Y` — the conditional covariance of `X` and `Y`
  given the σ-algebra `m`, defined as
  `𝔼[X · Y | m] - 𝔼[X | m] · 𝔼[Y | m]`.

## Main theorems

* `covariance_eq_expectation_condCovariance_add_covariance_condExp` —
  the Law of Total Covariance:
  `cov[X, Y; μ] = μ[condCov m μ X Y] + cov[μ[X|m], μ[Y|m]; μ]`.
* `lawOfTotalVariance` — the variance specialisation
  `Var[X; μ] = μ[condVar m μ X] + Var[μ[X|m]; μ]`.

## Proof sketch

The covariance bilinear identity gives
`cov[X, Y] = μ[X · Y] - μ[X] · μ[Y]`.

By the tower property `μ[X · Y] = μ[μ[X · Y | m]]`, we can write
the LHS as `μ[μ[X · Y | m]] - μ[X] · μ[Y]`.

By definition of `condCov`,
`μ[X · Y | m] = condCov m μ X Y + μ[X | m] · μ[Y | m]`.

Hence
`cov[X, Y] = μ[condCov m μ X Y] + μ[μ[X|m] · μ[Y|m]] - μ[X] · μ[Y]`.

The tower property again gives `μ[X] = μ[μ[X|m]]` and similarly for
`Y`. So the second piece is exactly
`cov[μ[X|m], μ[Y|m]; μ]`.

-/

namespace ProbabilityTheory

open MeasureTheory Filter

variable {Ω : Type*} {m₀ m : MeasurableSpace Ω}
  {μ : Measure Ω} {X Y : Ω → ℝ}

/-! ## §1. Conditional covariance -/

/-- The conditional covariance of two real-valued random variables
    `X` and `Y` given a sub-σ-algebra `m`.

    Defined as `𝔼[X · Y | m] - 𝔼[X | m] · 𝔼[Y | m]`. -/
noncomputable def condCovariance
    (m : MeasurableSpace Ω) (μ : Measure Ω) (X Y : Ω → ℝ) :
    Ω → ℝ :=
  μ[X * Y | m] - (μ[X | m]) * (μ[Y | m])

@[inherit_doc]
scoped notation "condCov[" X ", " Y " | " m "; " μ "]" =>
  ProbabilityTheory.condCovariance m μ X Y

/-- Conditional covariance is symmetric. -/
lemma condCovariance_comm
    (m : MeasurableSpace Ω) (μ : Measure Ω) (X Y : Ω → ℝ) :
    condCovariance m μ X Y = condCovariance m μ Y X := by
  unfold condCovariance
  congr 1
  · congr 1; ring_nf
  · ring

/-! ## §2. Law of Total Covariance — main theorem -/

/-- **Law of Total Covariance**: the unconditional covariance of
    `X` and `Y` decomposes into the expectation of the conditional
    covariance plus the covariance of the conditional expectations:

    `cov[X, Y; μ] = μ[condCov[X, Y | m; μ]] + cov[μ[X|m], μ[Y|m]; μ]`.

    Hypotheses (matching the standard Mathlib setup):
    * `hm : m ≤ m₀` — `m` is a sub-σ-algebra of the ambient `m₀`.
    * `μ` is a probability measure.
    * `X, Y` are L² (so `X·Y` is L¹ and conditional expectations exist).

    This is the foundational theorem powering Eriksson Bloque-4
    Proposition 6.1 (multiscale telescoping). -/
theorem covariance_eq_expectation_condCovariance_add_covariance_condExp
    [IsProbabilityMeasure μ] (hm : m ≤ m₀)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    covariance X Y μ =
      μ[condCovariance m μ X Y] +
      covariance (μ[X | m]) (μ[Y | m]) μ := by
  -- Step 1: apply covariance_eq_sub on both sides.
  have hX_int : Integrable X μ := hX.integrable (by simp)
  have hY_int : Integrable Y μ := hY.integrable (by simp)
  have hXY : Integrable (X * Y) μ := hX.integrable_mul hY
  have hcondX : MemLp (μ[X | m]) 2 μ := MemLp.condExp hX
  have hcondY : MemLp (μ[Y | m]) 2 μ := MemLp.condExp hY
  rw [covariance_eq_sub hX hY, covariance_eq_sub hcondX hcondY]
  -- Step 2: tower property (E[E[X|m]] = E[X], etc.).
  have h_int_condX : μ[μ[X | m]] = μ[X] := integral_condExp hm
  have h_int_condY : μ[μ[Y | m]] = μ[Y] := integral_condExp hm
  rw [h_int_condX, h_int_condY]
  -- Step 3: rewrite μ[X*Y] using tower property and condCov def.
  -- Goal:
  --   μ[X * Y] - μ[X] * μ[Y]
  --     = μ[condCovariance m μ X Y]
  --       + (μ[μ[X|m] * μ[Y|m]] - μ[X] * μ[Y])
  -- Cancel the -μ[X]*μ[Y] term:
  -- Need to show:
  --   μ[X * Y] = μ[condCovariance m μ X Y] + μ[μ[X|m] * μ[Y|m]]
  ring_nf
  -- After ring_nf the goal should be:
  --   μ[X * Y] - μ[μ[X|m] * μ[Y|m]] = μ[condCovariance m μ X Y]
  -- by linearity of integral:
  --   μ[X * Y] - μ[μ[X|m] * μ[Y|m]] = μ[X * Y - μ[X|m] * μ[Y|m]]
  -- and condCovariance m μ X Y is by definition
  --   μ[X * Y | m] - μ[X|m] * μ[Y|m]
  -- so its expectation is
  --   μ[μ[X * Y | m]] - μ[μ[X|m] * μ[Y|m]]
  --     = μ[X*Y] - μ[μ[X|m] * μ[Y|m]]   (tower property)
  -- closing the chain.
  --
  -- Detailed Lean execution:
  unfold condCovariance
  rw [integral_sub]
  · rw [integral_condExp hm]
  · -- integrability of μ[X*Y | m]
    exact integrable_condExp
  · -- integrability of μ[X|m] * μ[Y|m]
    exact (hcondX.integrable_mul hcondY)

/-! ## §3. Law of Total Variance — corollary -/

/-- **Law of Total Variance**: specialise LTC to `X = Y`:

    `Var[X; μ] = μ[condVar[X | m; μ]] + Var[μ[X | m]; μ]`.

    The conditional variance `condVar[X | m; μ]` is
    `condCov[X, X | m; μ]`. -/
theorem variance_eq_expectation_condVariance_add_variance_condExp
    [IsProbabilityMeasure μ] (hm : m ≤ m₀)
    (hX : MemLp X 2 μ) :
    variance X μ =
      μ[condCovariance m μ X X] + variance (μ[X | m]) μ := by
  -- Variance is covariance with itself.
  rw [variance_eq_covariance_self, variance_eq_covariance_self]
  exact covariance_eq_expectation_condCovariance_add_covariance_condExp hm hX hX

/-! ## §4. Coordination note (Yang–Mills programme) -/

/-
This file is the missing analytic foundation for the **multiscale
telescoping identity** in Eriksson's Bloque-4 paper (Proposition 6.1).

In the Yang–Mills setting:
* `Ω = G^|Λ_η|` (lattice gauge configurations).
* `μ = µ_η` (Wilson Gibbs measure).
* `m = σ_{a_k}` (σ-algebra generated by block-spin variables at
  scale `a_k`).
* `X, Y` = gauge-invariant local observables.

The LTC, applied iteratively along
`σ_{a_0} ⊃ σ_{a_1} ⊃ ⋯ ⊃ σ_{a_*}`, gives:

  Cov_{µ_η}(F, G) = Cov_{µ_a*}(F̃, G̃) + Σ_k R_k(F, G)

where R_k(F, G) = 𝔼_{µ_{a_{k+1}}}[Cov_{µ_{a_k} | σ_{a_{k+1}}}(F_k, G_k)]
is the conditional-covariance term at scale a_k.

Bloque-4 §6.2 then bounds each R_k(F, G) by the random-walk decay of
the propagator at scale a_k, and §6.3 sums geometrically over scales
to produce uniform UV suppression.

## Mathlib PR plan (suggested)

When ported to Mathlib, this file should:

1. Live alongside `Mathlib/Probability/Moments/Covariance.lean` as
   either a new section or a sibling file `CovarianceTotalLaw.lean`.
2. Add docstring-level cross-references to existing `condExp` /
   `covariance` API.
3. Optionally extend to vector-valued `X, Y` via the bilinear form
   in `CovarianceBilin.lean` (separate PR).

## Caveat

This file is currently in the YangMills tree at
`YangMills/MathlibUpstream/LawOfTotalCovariance.lean`. Once verified
by a Lean compiler and accepted into Mathlib, it should be **removed
from this project** to avoid duplication. The project's downstream
consumers (the multiscale telescoping in Branch I/II/III) would then
import it directly from `Mathlib.Probability.Moments.Covariance`.
-/

end ProbabilityTheory
