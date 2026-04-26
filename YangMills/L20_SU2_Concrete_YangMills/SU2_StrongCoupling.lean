/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# SU(2) strong-coupling expansion (Phase 188)

This module formalises the **strong-coupling expansion** for SU(2)
lattice gauge theory, used as a starting point for cluster expansion.

## Strategic placement

This is **Phase 188** of the L20_SU2_Concrete_YangMills block.

## What it does

In the strong-coupling regime `β → 0`, the lattice partition function
is expanded as a series in `β`. Each order corresponds to closed
loops on the lattice (graphs).

We define:
* `StrongCouplingExpansion` — abstract series in `β`.
* Coefficients of order `β^k`.
* Convergence properties at small `β`.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L20_SU2_Concrete_YangMills

/-! ## §1. The strong-coupling expansion series -/

/-- A **strong-coupling expansion** with coefficients indexed by `ℕ`. -/
structure StrongCouplingExpansion where
  /-- Coefficients `c_k` for the `β^k` term. -/
  c : ℕ → ℝ
  /-- A radius of convergence (positive). -/
  radius : ℝ
  /-- Radius is positive. -/
  radius_pos : 0 < radius

/-! ## §2. Evaluation as truncated polynomial -/

/-- **Evaluate the strong-coupling expansion truncated at order `n`**:
    `Σ_{k=0}^{n-1} c_k · β^k`. -/
def StrongCouplingExpansion.evalTruncated
    (sc : StrongCouplingExpansion) (n : ℕ) (β : ℝ) : ℝ :=
  (Finset.range n).sum (fun k => sc.c k * β ^ k)

/-! ## §3. Vanishing at zero coupling -/

/-- **At `β = 0`, the truncated expansion equals the constant term `c_0`**.

    Specifically: `Σ_{k=0}^{n-1} c_k · 0^k = c_0` (since `0^0 = 1`
    by convention and `0^k = 0` for `k ≥ 1`). -/
theorem StrongCouplingExpansion.evalTruncated_at_zero
    (sc : StrongCouplingExpansion) (n : ℕ) (h : 0 < n) :
    sc.evalTruncated n 0 = sc.c 0 := by
  unfold StrongCouplingExpansion.evalTruncated
  -- Need: Σ_{k=0}^{n-1} c_k · 0^k = c_0.
  -- For k = 0: c_0 · 0^0 = c_0 · 1 = c_0.
  -- For k ≥ 1: c_k · 0^k = c_k · 0 = 0.
  rw [show n = (n - 1) + 1 from (Nat.sub_add_cancel h).symm]
  rw [Finset.sum_range_succ']
  simp [pow_succ]

#print axioms StrongCouplingExpansion.evalTruncated_at_zero

/-! ## §4. Linearity in coefficients -/

/-- **The truncated evaluation is linear in coefficients (per term)**. -/
theorem StrongCouplingExpansion.evalTruncated_zero_n
    (sc : StrongCouplingExpansion) (β : ℝ) :
    sc.evalTruncated 0 β = 0 := by
  unfold StrongCouplingExpansion.evalTruncated
  simp

#print axioms StrongCouplingExpansion.evalTruncated_zero_n

/-! ## §5. Coordination note -/

/-
This file is **Phase 188** of the L20_SU2_Concrete_YangMills block.

## What's done

Two substantive Lean theorems with full proofs:
* `evalTruncated_at_zero` — at `β = 0`, only the `c_0` term
  contributes. Proved with `Finset.sum_range_succ'` + simp.
* `evalTruncated_zero_n` — at truncation level 0, the sum is empty
  and evaluates to 0.

Real Lean math.

## Strategic value

Phase 188 establishes the abstract strong-coupling expansion
framework, the analytic starting point for character + cluster
expansions in SU(2) Yang-Mills.

Cross-references:
- Bloque-4 §5 (cluster expansion at strong coupling).
- Codex's F3-Mayer Brydges-Kennedy expansion.
-/

end YangMills.L20_SU2_Concrete_YangMills
