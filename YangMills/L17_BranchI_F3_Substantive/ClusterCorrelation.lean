/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Cluster correlation function (Phase 155)

This module formalises the **cluster correlation function**: the
two-point function obtained from the cluster expansion that
captures the truncated correlations.

## Strategic placement

This is **Phase 155** of the L17_BranchI_F3_Substantive block.

## What it does

For a connected polymer expansion, the truncated two-point
correlator is

  ⟨A(x); B(y)⟩_T = ⟨A(x) B(y)⟩ − ⟨A(x)⟩ ⟨B(y)⟩
                  = Σ_{X ∋ x, X ∋ y} cluster_weight(X).

This is the cluster correlation function. We define:
* `ClusterCorrelator` — abstract two-point function.
* Symmetry, non-negativity bounds.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L17_BranchI_F3_Substantive

/-! ## §1. The abstract cluster correlator -/

/-- An **abstract cluster correlator** between two points. -/
structure ClusterCorrelator (Site : Type*) where
  /-- The truncated two-point function. -/
  C : Site → Site → ℝ
  /-- Symmetry: `C(x, y) = C(y, x)`. -/
  symm : ∀ x y : Site, C x y = C y x

/-! ## §2. The diagonal vanishes for centered observables -/

/-- A **centered cluster correlator** vanishes on the diagonal. -/
structure CenteredClusterCorrelator (Site : Type*)
    extends ClusterCorrelator Site where
  /-- Vanishing on the diagonal (centered observables). -/
  diag_zero : ∀ x : Site, C x x = 0

/-! ## §3. Pointwise upper bound -/

/-- **A bound on `|C x y|`** by a function of the "distance" between
    `x` and `y` (abstract). -/
structure ClusterCorrelatorBound (Site : Type*) where
  /-- The correlator. -/
  cc : ClusterCorrelator Site
  /-- The distance function. -/
  d : Site → Site → ℝ
  /-- Distance is non-negative. -/
  d_nonneg : ∀ x y : Site, 0 ≤ d x y
  /-- The bound function. -/
  bound : ℝ → ℝ
  /-- Bound is non-negative. -/
  bound_nonneg : ∀ r : ℝ, 0 ≤ bound r
  /-- The pointwise bound: `|C x y| ≤ bound (d x y)`. -/
  point_bound : ∀ x y : Site, |cc.C x y| ≤ bound (d x y)

/-! ## §4. Symmetry of the bound -/

/-- **The pointwise bound is symmetric**: `|C x y| ≤ bound (d x y)` is
    equivalent to the symmetric statement when `d` is symmetric. -/
theorem ClusterCorrelatorBound.bound_symm
    {Site : Type*} (B : ClusterCorrelatorBound Site)
    (h_d_symm : ∀ x y : Site, B.d x y = B.d y x)
    (x y : Site) :
    |B.cc.C x y| ≤ B.bound (B.d y x) := by
  rw [← h_d_symm x y]
  exact B.point_bound x y

#print axioms ClusterCorrelatorBound.bound_symm

/-! ## §5. Non-negativity of the absolute correlator -/

/-- **The absolute correlator `|C x y|` is non-negative**. -/
theorem abs_correlator_nonneg
    {Site : Type*} (cc : ClusterCorrelator Site) (x y : Site) :
    0 ≤ |cc.C x y| := abs_nonneg _

/-! ## §6. Coordination note -/

/-
This file is **Phase 155** of the L17_BranchI_F3_Substantive block.

## What's done

A clean abstract `ClusterCorrelator` + `ClusterCorrelatorBound`
structure with:
* `ClusterCorrelatorBound.bound_symm` — bound is symmetric.
* `abs_correlator_nonneg` — absolute correlator is non-negative.

## Strategic value

Phase 155 establishes the abstract two-point-correlator framework
that downstream files (exponential decay, terminal clustering) can
target.

Cross-references:
- Bloque-4 §5 (terminal KP gives exponential cluster).
- Codex's `ClusterCorrelatorBound`.
-/

end YangMills.L17_BranchI_F3_Substantive
