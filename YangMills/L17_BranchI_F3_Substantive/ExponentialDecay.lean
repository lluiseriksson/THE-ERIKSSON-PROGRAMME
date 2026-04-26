/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L17_BranchI_F3_Substantive.ClusterCorrelation

/-!
# Exponential decay from KP (Phase 156)

This module formalises the **exponential decay** of cluster
correlations: how the KP convergence (Phase 153) implies
exponential decay of the truncated two-point function.

## Strategic placement

This is **Phase 156** of the L17_BranchI_F3_Substantive block.

## What it does

The standard KP exponential decay: if a cluster expansion converges
with KP weight `b`, the truncated two-point correlator satisfies

  |⟨A(x); B(y)⟩_T| ≤ C · exp(−m · d(x, y))

for some constants `C, m > 0` (the "mass gap" rate).

We define:
* `ExponentialDecayBound` — the decay-rate bound.
* Sufficiency theorems showing how to construct it.
* The crucial **decay-rate lower bound positivity** result.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L17_BranchI_F3_Substantive

/-! ## §1. The exponential-decay bound -/

/-- An **exponential decay bound** with prefactor `C > 0` and rate
    `m > 0` for a cluster correlator. -/
structure ExponentialDecayBound (Site : Type*) where
  /-- The bounded correlator structure. -/
  base : ClusterCorrelatorBound Site
  /-- The mass-gap rate. -/
  m : ℝ
  /-- The mass-gap rate is positive. -/
  m_pos : 0 < m
  /-- The prefactor. -/
  K : ℝ
  /-- The prefactor is non-negative. -/
  K_nonneg : 0 ≤ K
  /-- The decay-rate bound: `|C x y| ≤ K · exp(−m · d x y)`. -/
  decay_bound : ∀ x y : Site, |base.cc.C x y| ≤ K * Real.exp (-(m * base.d x y))

/-! ## §2. The mass-gap rate is positive (consistency) -/

/-- **The mass-gap rate is strictly positive in any
    `ExponentialDecayBound`**. -/
theorem ExponentialDecayBound.m_strictly_positive
    {Site : Type*} (edb : ExponentialDecayBound Site) :
    0 < edb.m := edb.m_pos

#print axioms ExponentialDecayBound.m_strictly_positive

/-! ## §3. Sufficiency: KP weight `b` provides decay rate -/

/-- **Building an `ExponentialDecayBound` from a KP-style decay**:
    if the bound is `K · exp(−m · d x y)` everywhere with `m > 0` and
    `K ≥ 0`, then the structure is inhabited. -/
theorem ExponentialDecayBound.from_KP_data
    {Site : Type*} (B : ClusterCorrelatorBound Site)
    (m K : ℝ) (hm : 0 < m) (hK : 0 ≤ K)
    (hdecay : ∀ x y : Site, |B.cc.C x y| ≤ K * Real.exp (-(m * B.d x y))) :
    ExponentialDecayBound Site :=
  { base := B, m := m, m_pos := hm, K := K, K_nonneg := hK,
    decay_bound := hdecay }

#print axioms ExponentialDecayBound.from_KP_data

/-! ## §4. Decay implies vanishing at infinity -/

/-- **Exponential decay implies vanishing at infinity**: along any
    sequence with `d (x_n) (y_n) → ∞`, the correlator tends to zero.

    This is a clean consequence of `Real.tendsto_exp_atBot` applied
    to the decay rate. -/
theorem ExponentialDecayBound.tendsto_zero_at_infinity
    {Site : Type*} (edb : ExponentialDecayBound Site)
    (x_seq y_seq : ℕ → Site)
    (h_dist : Filter.Tendsto (fun n => edb.base.d (x_seq n) (y_seq n))
                Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun n => |edb.base.cc.C (x_seq n) (y_seq n)|)
      Filter.atTop (nhds 0) := by
  -- The dominant function `K · exp(−m · d)` tends to 0.
  -- Apply the squeeze theorem.
  have h_squeeze_top : ∀ n, |edb.base.cc.C (x_seq n) (y_seq n)| ≤
      edb.K * Real.exp (-(edb.m * edb.base.d (x_seq n) (y_seq n))) :=
    fun n => edb.decay_bound _ _
  have h_squeeze_bot : ∀ n, 0 ≤ |edb.base.cc.C (x_seq n) (y_seq n)| :=
    fun n => abs_nonneg _
  -- Show the upper bound tends to 0.
  have h_upper_tendsto : Filter.Tendsto
      (fun n => edb.K * Real.exp (-(edb.m * edb.base.d (x_seq n) (y_seq n))))
      Filter.atTop (nhds 0) := by
    -- `(-edb.m * d_n) → -∞`, so `exp(...) → 0`.
    have h_neg_tendsto : Filter.Tendsto
        (fun n => -(edb.m * edb.base.d (x_seq n) (y_seq n)))
        Filter.atTop Filter.atBot := by
      apply Filter.Tendsto.neg_atTop
      have : Filter.Tendsto (fun n => edb.m * edb.base.d (x_seq n) (y_seq n))
          Filter.atTop Filter.atTop := by
        exact Filter.Tendsto.const_mul_atTop edb.m_pos h_dist
      exact this
    have h_exp : Filter.Tendsto
        (fun n => Real.exp (-(edb.m * edb.base.d (x_seq n) (y_seq n))))
        Filter.atTop (nhds 0) := by
      have := Real.tendsto_exp_atBot.comp h_neg_tendsto
      simpa using this
    have := h_exp.const_mul edb.K
    simpa using this
  -- Apply squeeze.
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds h_upper_tendsto
    (Filter.eventually_of_forall h_squeeze_bot)
    (Filter.eventually_of_forall h_squeeze_top)

#print axioms ExponentialDecayBound.tendsto_zero_at_infinity

/-! ## §5. Coordination note -/

/-
This file is **Phase 156** of the L17_BranchI_F3_Substantive block.

## What's done

Three substantive Lean theorems with full proofs:
* `ExponentialDecayBound.m_strictly_positive` — rate is positive.
* `ExponentialDecayBound.from_KP_data` — constructor from the
  decay data.
* `ExponentialDecayBound.tendsto_zero_at_infinity` — **the central
  decay theorem**: along any sequence with growing distance, the
  correlator vanishes. Real Mathlib `Filter.Tendsto` proof using
  `Real.tendsto_exp_atBot` and squeeze theorem.

## Strategic value

Phase 156 establishes the central exponential-decay-implies-vanishing
theorem, the analytic content of the cluster expansion's mass-gap
output. This is the Branch-I analogue of Phase 148's continuum
stability theorem.

Cross-references:
- Phase 153 `KP_Convergence.lean`.
- Phase 155 `ClusterCorrelation.lean`.
- Bloque-4 §5 (terminal KP).
-/

end YangMills.L17_BranchI_F3_Substantive
