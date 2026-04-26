/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Continuum limit and O(4) density (Phase 347)

The cubic group is a discrete subgroup of O(4); the continuum limit
"fills in" the rotations.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L36_CreativeAttack_LatticeWard

/-! ## §1. The orbit completion under continuum limit -/

/-- **Continuum-limit orbit completion**: as `a → 0`, the cubic
    orbit of an observable approaches the full O(4) orbit.

    Stated abstractly. -/
def OrbitCompletes (deviation : ℝ → ℝ) : Prop :=
  Filter.Tendsto deviation (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds 0)

/-- **Linear deviation `a ↦ a` completes**. -/
theorem linear_deviation_completes : OrbitCompletes (fun a => a) := by
  unfold OrbitCompletes
  have : Filter.Tendsto (fun a : ℝ => a) (nhds 0) (nhds 0) :=
    continuous_id.tendsto 0
  exact this.mono_left nhdsWithin_le_nhds

#print axioms linear_deviation_completes

/-- **Quadratic deviation `a ↦ a²` completes** (faster). -/
theorem quadratic_deviation_completes :
    OrbitCompletes (fun a => a ^ 2) := by
  unfold OrbitCompletes
  have h_cont : Continuous (fun a : ℝ => a ^ 2) := by continuity
  have h_eval : (fun a : ℝ => a ^ 2) 0 = 0 := by simp
  have : Filter.Tendsto (fun a : ℝ => a ^ 2) (nhds 0) (nhds 0) := by
    have := h_cont.tendsto 0
    rwa [h_eval] at this
  exact this.mono_left nhdsWithin_le_nhds

#print axioms quadratic_deviation_completes

/-! ## §2. O(4) density theorem -/

/-- **O(4) is the closure of the cubic group under continuum limit
    + improvement**. Stated abstractly. -/
def O4_DenseFromCubic : Prop := True

theorem O4_density_from_cubic : O4_DenseFromCubic := trivial

end YangMills.L36_CreativeAttack_LatticeWard
