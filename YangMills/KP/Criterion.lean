/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.KP.Cluster

/-!
# KP2b (convergence side) — the Kotecký–Preiss smallness criterion

The convergence of the cluster expansion (`docs/kp-cluster-expansion-plan.md`, E4 /
FV Thm 5.4) holds under the **Kotecký–Preiss criterion**: there is a weight
`a : Polymer → ℝ≥0` such that, for every polymer `X`,

  `∑_{Y incompatible with X} ‖z(Y)‖ · exp(a(Y)) ≤ a(X)`.

This is the precise hypothesis the (deferred) inductive convergence proof needs.  This
file pins it down as a Lean predicate (finite volume, so the sum is a `Finset` sum)
and proves its first elementary consequence: under the criterion, every activity is
dominated by its weight, `‖z(X)‖ ≤ a(X)`.  That bound is the seed of the inductive
KP estimate — the base from which the cluster-size induction (E4) departs.

Defining the criterion does not prove convergence; it makes the convergence theorem
*statable*, which is the honest next structural step on the convergence side.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.KP

open scoped Classical BigOperators

variable (P : PolymerSystem)

/-- The **Kotecký–Preiss criterion** for a weight `a : Polymer → ℝ` (finite volume):
`a` is nonnegative and, for every polymer `X`, the weighted activity of all polymers
incompatible with `X` (including `X` itself, by the hard core) is bounded by `a(X)`:
`∑_{Y : incomp X Y} ‖z(Y)‖ · exp(a(Y)) ≤ a(X)`.  This is the standard smallness
condition under which the cluster expansion converges (E4). -/
def KPCriterion [Fintype P.Polymer] (a : P.Polymer → ℝ) : Prop :=
  (∀ X, 0 ≤ a X) ∧
  ∀ X, ∑ Y ∈ Finset.univ.filter (fun Y => P.incomp X Y),
      ‖P.activity Y‖ * Real.exp (a Y) ≤ a X

/-- **First consequence of the KP criterion: activities are dominated by the weight.**
Because the hard core makes `X` incompatible with itself, the `X`-term `‖z(X)‖·exp(a(X))`
appears in (and, all terms being nonnegative, is bounded by) the criterion sum, so
`‖z(X)‖·exp(a(X)) ≤ a(X)`.  Since `a(X) ≥ 0` gives `exp(a(X)) ≥ 1`, we get
`‖z(X)‖ ≤ a(X)`.  This is the base estimate of the inductive KP convergence bound. -/
theorem kp_activity_le [Fintype P.Polymer] {a : P.Polymer → ℝ}
    (h : KPCriterion P a) (X : P.Polymer) : ‖P.activity X‖ ≤ a X := by
  classical
  obtain ⟨hnn, hsum⟩ := h
  have hXmem : X ∈ Finset.univ.filter (fun Y => P.incomp X Y) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ X, P.incomp_self X⟩
  have hterm : ‖P.activity X‖ * Real.exp (a X) ≤
      ∑ Y ∈ Finset.univ.filter (fun Y => P.incomp X Y),
        ‖P.activity Y‖ * Real.exp (a Y) :=
    Finset.single_le_sum
      (fun Y _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) hXmem
  have h1 : ‖P.activity X‖ * Real.exp (a X) ≤ a X := le_trans hterm (hsum X)
  have hexp : (1 : ℝ) ≤ Real.exp (a X) := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (hnn X)
  calc ‖P.activity X‖ = ‖P.activity X‖ * 1 := (mul_one _).symm
    _ ≤ ‖P.activity X‖ * Real.exp (a X) :=
        mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
    _ ≤ a X := h1

end YangMills.KP
