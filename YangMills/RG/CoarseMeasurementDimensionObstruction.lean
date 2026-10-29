/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib

/-!
# Dimension obstruction for factorized coarse penalties

This module proves the finite-dimensional kernel-intersection step. It does
not construct a lattice Fourier band or prove the concrete lattice dimension
and energy estimates. Those remain separate obligations in the analytic note
`docs/FLAT-COARSE-RANK-OBSTRUCTION-20261029.md`.

A nonlinear penalty after a linear measurement vanishes on its kernel when
the penalty vanishes at zero. A subspace larger than the measurement dimension
plus the rank of a fine repair therefore contains an unseen nonzero vector.
No positivity, symmetry or norm bound on the repair is needed for this step.
-/

namespace YangMills.RG

open Module

section Algebra

variable {E F G : Type*}
variable [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
variable [AddCommGroup G] [Module ℝ G]

/-- Rank-nullity supplies a nonzero vector invisible to both maps.
The repair contributes the dimension of its range, not its whole codomain. -/
theorem exists_unseen_of_finrank_lt_measurement_add_repair
    (S : Submodule ℝ E) (C : E →ₗ[ℝ] F) (V : E →ₗ[ℝ] G)
    (hdim : finrank ℝ F + finrank ℝ (LinearMap.range V) < finrank ℝ S) :
    ∃ x : E, x ∈ S ∧ x ≠ 0 ∧ C x = 0 ∧ V x = 0 := by
  classical
  let f : S →ₗ[ℝ] F × LinearMap.range V :=
    (C.prod V.rangeRestrict).comp S.subtype
  have hnotinj : ¬ Function.Injective f := by
    intro hinj
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_prod] at hle
    exact (not_le_of_gt hdim) hle
  have hex : ∃ x : S, x ≠ 0 ∧ f x = 0 := by
    by_contra hnone
    push_neg at hnone
    apply hnotinj
    intro x y hxy
    have hz : f (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hsub : x - y = 0 := by
      by_contra hne
      exact hnone (x - y) hne hz
    exact sub_eq_zero.mp hsub
  rcases hex with ⟨x, hx, hfx⟩
  refine ⟨x, x.property, ?_, ?_, ?_⟩
  · intro hz
    apply hx
    exact Subtype.ext hz
  · have hh := congrArg Prod.fst hfx
    simpa [f] using hh
  · have hh := congrArg (fun p : F × LinearMap.range V => (p.2 : G)) hfx
    simpa [f] using hh

end Algebra

section Energy

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]

/-- A low-energy subspace exceeding the available dimension/rank refutes a
full-space bound, even for a nonlinear coarse penalty with no regularity. -/
theorem factorized_coercivity_false_of_dimension_budget
    (S : Submodule ℝ E) (C : E →ₗ[ℝ] F) (V : E →ₗ[ℝ] E)
    (energy : E → ℝ) (Phi : F → ℝ) (hPhi : Phi 0 = 0)
    (b c : ℝ) (hbc : b < c)
    (hband : ∀ x : E, x ∈ S → energy x ≤ b * ‖x‖ ^ 2)
    (hdim : finrank ℝ F + finrank ℝ (LinearMap.range V) < finrank ℝ S) :
    ¬ ∀ x : E,
      c * ‖x‖ ^ 2 ≤ energy x + Phi (C x) + inner ℝ x (V x) := by
  intro hbound
  rcases exists_unseen_of_finrank_lt_measurement_add_repair S C V hdim with
    ⟨x, hxS, hx, hCx, hVx⟩
  have hpos : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hlo : c * ‖x‖ ^ 2 ≤ energy x := by
    simpa [hCx, hVx, hPhi] using hbound x
  have hhi := hband x hxS
  have hstrict := mul_lt_mul_of_pos_right hbc hpos
  linarith

/-- Every full-space repair must pay the dimension/rank budget of each
subspace strictly below the proposed coercivity threshold. -/
theorem factorized_coercivity_dimension_budget
    (S : Submodule ℝ E) (C : E →ₗ[ℝ] F) (V : E →ₗ[ℝ] E)
    (energy : E → ℝ) (Phi : F → ℝ) (hPhi : Phi 0 = 0)
    (b c : ℝ) (hbc : b < c)
    (hband : ∀ x : E, x ∈ S → energy x ≤ b * ‖x‖ ^ 2)
    (hbound : ∀ x : E,
      c * ‖x‖ ^ 2 ≤ energy x + Phi (C x) + inner ℝ x (V x)) :
    finrank ℝ S ≤ finrank ℝ F + finrank ℝ (LinearMap.range V) := by
  by_contra hfail
  exact factorized_coercivity_false_of_dimension_budget S C V energy Phi hPhi b c
    hbc hband (lt_of_not_ge hfail) hbound

end Energy

end YangMills.RG
