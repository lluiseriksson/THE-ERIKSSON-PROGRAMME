/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Scale sequences for an honest `a → 0` question

This module only records a positive lattice spacing and its convergence to
zero.  It does not attach a continuum configuration space, a measure, or a
Yang--Mills interpretation to that numerical limit.

Oracle target: standard Lean/Mathlib axioms only. No sorry, no project axioms.
-/

namespace YangMills.Continuum

open Filter Topology

/-- A sequence of strictly positive lattice spacings tending to zero. -/
structure ScaleSequence where
  spacing : ℕ → ℝ
  spacing_pos : ∀ n, 0 < spacing n
  tendsToZero : Tendsto spacing atTop (𝓝 0)

/-- The explicit obligation that a continuum-facing spacing convention
agrees with some spacing already used by a repository construction.  C0 does
not identify this with the RG `scaleSpacing` convention automatically. -/
def ScaleConventionCompatible
    (scale : ScaleSequence) (repositorySpacing : ℕ → ℝ) : Prop :=
  ∀ n, scale.spacing n = repositorySpacing n

/-- The canonical explicit choice `aₙ = 1 / (n + 1)`. -/
noncomputable def reciprocalScale : ScaleSequence where
  spacing := fun n => 1 / ((n : ℝ) + 1)
  spacing_pos := by
    intro n
    positivity
  tendsToZero := tendsto_one_div_add_atTop_nhds_zero_nat

@[simp]
theorem reciprocalScale_spacing (n : ℕ) :
    reciprocalScale.spacing n = 1 / ((n : ℝ) + 1) :=
  rfl

theorem reciprocalScale_spacing_ne_zero (n : ℕ) :
    reciprocalScale.spacing n ≠ 0 :=
  ne_of_gt (reciprocalScale.spacing_pos n)

end YangMills.Continuum
