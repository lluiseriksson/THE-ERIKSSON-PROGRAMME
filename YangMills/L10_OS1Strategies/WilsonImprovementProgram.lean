/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Wilson improvement program for OS1 (Strategy E1)

This module formalises **Strategy E1** from
`CREATIVE_ATTACKS_OPENING_TREE.md` (Phase 87): the **Symanzik /
Wilson coefficient improvement program** approach to OS1 (full O(4)
Euclidean covariance).

## Strategic placement

This is **Phase 108** of the L10_OS1Strategies block (Phases 108-112).

## The argument (Symanzik 1983; Lüscher-Weisz 1985)

For the Wilson lattice gauge action, the leading anisotropies in
the continuum limit are O(η²)-suppressed.

A **Wilson coefficient expansion** writes the lattice action as

  `S_lattice = S_continuum + η² · O(2) + η⁴ · O(4) + ...`

where each `O(d)` is a sum of dimension-d local operators. The
hypercubic-only operators (those that break O(4) but preserve W4)
have specific dimensions; in 4D pure gauge theory:

* dim-2: none (no O(4)-symmetric dimension-2 gauge-invariant
  operator other than the constant).
* dim-4: only the kinetic term `Tr F_µν F^µν` (O(4)-symmetric).
* dim-6 and higher: include both O(4)-symmetric and W4-only
  operators.

By **dimensional regularisation**: in the continuum limit `η → 0`,
operators of dimension `d > 4` get suppressed by `η^(d-4) → 0`.
Hence all hypercubic-only operators (which start at dim-6) vanish,
restoring full O(4) symmetry.

## Status

This strategy is **physically standard** but its rigorous Lean
formalisation requires:
* Effective field theory machinery (operator expansion).
* Dimensional analysis.
* Power counting in the continuum limit.

These are substantial Mathlib upstream gaps. This file provides the
**structural skeleton** indicating where the rigorous proof would go.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.

-/

namespace YangMills.L10_OS1Strategies

open MeasureTheory

/-! ## §1. Operator dimension data -/

/-- An **operator dimension specification**: each lattice operator
    has a dimension `d` and a hypercubic-symmetry classification
    (`O(4)`-symmetric, `W4`-symmetric only, or breaking both). -/
structure OperatorDimension where
  /-- The dimension of the operator (in mass units). -/
  dim : ℕ
  /-- Whether the operator preserves full O(4). -/
  isO4Symmetric : Bool
  /-- Whether the operator at least preserves W4. -/
  isW4Symmetric : Bool
  /-- Consistency: full O(4) ⊂ W4. -/
  consistency : isO4Symmetric → isW4Symmetric := by
    intro h; exact h

/-! ## §2. The Wilson expansion -/

/-- A **Wilson coefficient expansion**: the lattice action expressed
    as a sum of continuum operators with Wilson coefficients. -/
structure WilsonExpansion where
  /-- Operator labels. -/
  Operator : Type
  /-- Each operator has a dimension. -/
  opDim : Operator → OperatorDimension
  /-- The Wilson coefficients (η-dependent). -/
  coefficient : Operator → ℝ → ℝ
  /-- Each coefficient is bounded by the appropriate η-power. -/
  coefficient_bound : ∀ (O : Operator) (η : ℝ), 0 < η →
    |coefficient O η| ≤ η ^ ((opDim O).dim - 4)

/-! ## §3. The OS1 restoration claim -/

/-- The **OS1 restoration via Wilson improvement**: in the continuum
    limit, the Wilson coefficients of all `W4`-only operators
    (hypercubic-symmetric but not full O(4)-symmetric) tend to zero. -/
def WilsonImprovementOS1
    (W : WilsonExpansion) : Prop :=
  -- For every W4-only operator (not full O(4)):
  -- the Wilson coefficient → 0 as η → 0.
  ∀ (O : W.Operator),
    (W.opDim O).isW4Symmetric →
    ¬ (W.opDim O).isO4Symmetric →
    Filter.Tendsto (W.coefficient O) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

/-! ## §4. The dimensional analysis theorem -/

/-- **Wilson improvement ⇒ OS1 restoration (abstract)**:
    if every hypercubic-only operator has dimension > 4, then by
    dimensional analysis its Wilson coefficient vanishes in the
    continuum limit.

    Proof: take witness δ = min ε 1, ensuring η ≤ 1 in the
    metric-close branch. Then η^(d-4) ≤ η^1 = η < ε. -/
theorem wilsonImprovement_OS1_from_dimension
    (W : WilsonExpansion)
    (h_dim :
      ∀ (O : W.Operator),
        (W.opDim O).isW4Symmetric →
        ¬ (W.opDim O).isO4Symmetric →
        4 < (W.opDim O).dim) :
    WilsonImprovementOS1 W := by
  intro O h_W4 h_not_O4
  have hd := h_dim O h_W4 h_not_O4
  have h_bound := W.coefficient_bound O
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  -- Take δ := min ε 1 to enforce η ≤ 1 in the proof.
  refine ⟨min ε 1, lt_min hε one_pos, fun η hη_pos hη_close => ?_⟩
  rw [Real.dist_eq, sub_zero] at hη_close ⊢
  have h_pos : (0 : ℝ) < η := hη_pos
  -- |η| < min ε 1 ⟹ η < ε ∧ η < 1
  rw [abs_of_pos h_pos] at hη_close
  have h_η_lt_ε : η < ε := lt_of_lt_of_le hη_close (min_le_left _ _)
  have h_η_lt_1 : η < 1 := lt_of_lt_of_le hη_close (min_le_right _ _)
  have h_η_le_1 : η ≤ 1 := le_of_lt h_η_lt_1
  -- |c_O(η)| ≤ η^(d-4)
  have h_b := h_bound η h_pos
  have h_d_minus_4 : 1 ≤ (W.opDim O).dim - 4 := by omega
  -- η^(d-4) ≤ η^1 = η for 0 < η ≤ 1 and d-4 ≥ 1.
  have h_pow_le : η ^ ((W.opDim O).dim - 4) ≤ η := by
    calc η ^ ((W.opDim O).dim - 4)
        ≤ η ^ 1 :=
          pow_le_pow_of_le_one h_pos.le h_η_le_1 h_d_minus_4
      _ = η := pow_one η
  -- Combine.
  calc |W.coefficient O η|
      ≤ η ^ ((W.opDim O).dim - 4) := h_b
    _ ≤ η := h_pow_le
    _ < ε := h_η_lt_ε

#print axioms wilsonImprovement_OS1_from_dimension

/-! ## §5. Coordination note -/

/-
This file is **Phase 108** of the L10_OS1Strategies block.

## Status

* `OperatorDimension`, `WilsonExpansion`, `WilsonImprovementOS1`
  data structures.
* `wilsonImprovement_OS1_from_dimension` theorem with **a partial
  proof** that has a logical gap in the η > 1 case (where the
  metric-distance argument doesn't directly give η ≤ 1).

## Honest assessment

The theorem proof is **structurally correct** but has a Lean-execution
issue at η > 1 case. The cleanest fix is to take the witness δ = min ε 1;
that ensures η ≤ 1 at the proof's branch.

The η > 1 case is "logically inaccessible" in the limit η → 0⁺, but
Lean's type checker requires us to handle it explicitly.

## What's done

The strategy E1 (Wilson improvement) is **structurally captured**
with the dimensional analysis chain:
  d > 4 ⇒ |c_O(η)| ≤ η^(d-4) → 0 as η → 0⁺.

The substantive content (verifying that all W4-only operators have
dimension > 4 in 4D pure gauge theory) is left as a hypothesis,
which is itself a classical result of Symanzik / Lüscher-Weisz.

Cross-references:
- `CREATIVE_ATTACKS_OPENING_TREE.md` Strategy E1 (Phase 87).
- Phase 101: `WightmanReconstruction_Conditional.lean`
  (where OS1 is the input).
- Symanzik 1983; Lüscher-Weisz 1985.
-/

end YangMills.L10_OS1Strategies
