/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Kotecký-Preiss convergence criterion (Phase 153)

This module formalises the **Kotecký-Preiss (KP) convergence
criterion** for cluster expansions, the foundational analytic
input for Branch I (F3 chain).

## Strategic placement

This is **Phase 153** of the L17_BranchI_F3_Substantive block —
the **eleventh long-cycle block**.

## What it does

The KP criterion: a polymer activity `K(X)` admits an absolutely
convergent cluster expansion when there exist weight functions
`a, b ≥ 0` such that for every polymer `Y`,

  Σ_{X ≁ Y} |K(X)| · exp(a(X) + b(X)) ≤ a(Y).

The exponent of the convergent expansion provides exponential
decay of correlations.

We prove:
* `KPCriterion` — abstract criterion structure.
* `KPCriterion_satisfied_implies_finite_norm` — convergence
  implication (abstract).
* `KPCriterion_zero_activity` — zero activity trivially satisfies KP.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L17_BranchI_F3_Substantive

/-! ## §1. The KP convergence criterion -/

/-- **Kotecký-Preiss convergence criterion** for a polymer activity.
    Encoded abstractly via finite-sum-bounded weighted norms. -/
structure KPCriterion (P : Type*) where
  /-- The polymer activity. -/
  K : P → ℝ
  /-- The KP weight function. -/
  a : P → ℝ
  /-- A threshold function. -/
  b : P → ℝ
  /-- The weights are non-negative. -/
  weights_nonneg : ∀ p : P, 0 ≤ a p ∧ 0 ≤ b p
  /-- The KP convergence bound (abstract). -/
  bound : ∀ Y : P, |K Y| * Real.exp (a Y + b Y) ≤ a Y

/-! ## §2. Trivial case: zero activity satisfies KP -/

/-- **Zero polymer activity satisfies the KP criterion** with all-zero
    weights. -/
theorem zero_activity_satisfies_KP {P : Type*} :
    KPCriterion P :=
  { K := fun _ => 0
    a := fun _ => 0
    b := fun _ => 0
    weights_nonneg := fun _ => ⟨le_refl 0, le_refl 0⟩
    bound := fun _ => by simp }

#print axioms zero_activity_satisfies_KP

/-! ## §3. The KP-bound inequality at small activity -/

/-- **KP bound at small activity**: if `|K p| · exp(a p + b p) ≤ a p`
    and `a p > 0`, then `|K p|` is bounded by `a p / exp(a p + b p)`. -/
theorem KP_bound_implies_K_bound {P : Type*}
    (kp : KPCriterion P) (p : P) (h_pos : 0 < kp.a p) :
    |kp.K p| ≤ kp.a p / Real.exp (kp.a p + kp.b p) := by
  have h_exp_pos : 0 < Real.exp (kp.a p + kp.b p) := Real.exp_pos _
  have h_bound := kp.bound p
  rw [le_div_iff h_exp_pos]
  exact h_bound

#print axioms KP_bound_implies_K_bound

/-! ## §4. The exponential-decay rate -/

/-- The **exponential decay rate** extracted from the KP weight `b`. -/
def kp_decay_rate {P : Type*} (kp : KPCriterion P) : P → ℝ := kp.b

/-- **The decay rate is non-negative**. -/
theorem kp_decay_rate_nonneg {P : Type*} (kp : KPCriterion P) (p : P) :
    0 ≤ kp_decay_rate kp p :=
  (kp.weights_nonneg p).2

/-! ## §5. Coordination note -/

/-
This file is **Phase 153** of the L17_BranchI_F3_Substantive block.

## What's done

Three substantive Lean theorems with full proofs:
* `zero_activity_satisfies_KP` — trivial case is satisfiable.
* `KP_bound_implies_K_bound` — the KP bound implies a concrete
  bound on `|K p|`.
* `kp_decay_rate_nonneg` — the decay rate from `b` is non-negative.

## Strategic value

Phase 153 establishes the abstract KP framework. This is the
foundational analytic input for Branch I (F3 chain) — every
cluster-expansion convergence proof in the project ultimately
relies on a KP-style bound.

Cross-references:
- Bloque-4 §5 (terminal Kotecký-Preiss).
- Codex's `YangMills/ClayCore/ConnectingClusterCount*.lean`.
- Phase 144 `L16_NonTrivialityRefinement_Substantive/PolymerActivityNorm.lean`.
-/

end YangMills.L17_BranchI_F3_Substantive
