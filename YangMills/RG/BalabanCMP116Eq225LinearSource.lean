/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq225SourceEnergy

/-!
# CMP116 equation (2.25): linear localized sources

This module produces the source-energy hypothesis of (2.25) for a source of
the literal form `J (P_S X)`.  The squared source is bounded by the squared
`L²` operator norm of `J` times the localized field energy.  Thus the remaining
model-specific obligation is an operator-norm estimate for the concrete
CMP116 source kernel, not a bound uniform in the unbounded Gaussian field.
-/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace YangMills.RG

/-- Exact squared norm of the localized coordinate projection. -/
theorem dotProduct_projection_mulVec_self
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (x : ι → ℝ) :
    (cmp116Eq223CoordinateProjection S *ᵥ x) ⬝ᵥ
        (cmp116Eq223CoordinateProjection S *ᵥ x) =
      ∑ i ∈ S, x i ^ 2 := by
  simp only [cmp116Eq223CoordinateProjection, mulVec_diagonal, dotProduct]
  calc
    ∑ i, ((if i ∈ S then 1 else 0) * x i) *
        ((if i ∈ S then 1 else 0) * x i) =
      ∑ i, if i ∈ S then x i ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        split_ifs <;> simp [pow_two]
    _ = ∑ i ∈ S, x i ^ 2 := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext i
        simp
      · intro i hi
        simp at hi
        rfl

/-- The canonical source-energy estimate for a matrix source applied to the
localized outer field. -/
theorem dotProduct_linearLocalizedSource_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (J : Matrix ι ι ℝ) (x : ι → ℝ) :
    (J *ᵥ (cmp116Eq223CoordinateProjection S *ᵥ x)) ⬝ᵥ
        (J *ᵥ (cmp116Eq223CoordinateProjection S *ᵥ x)) ≤
      ‖J‖ ^ 2 * ∑ i ∈ S, x i ^ 2 := by
  calc
    (J *ᵥ (cmp116Eq223CoordinateProjection S *ᵥ x)) ⬝ᵥ
        (J *ᵥ (cmp116Eq223CoordinateProjection S *ᵥ x)) ≤
      ‖J‖ ^ 2 *
        ((cmp116Eq223CoordinateProjection S *ᵥ x) ⬝ᵥ
          (cmp116Eq223CoordinateProjection S *ᵥ x)) :=
      dotProduct_mulVec_self_le_l2_opNorm_sq J _
    _ = ‖J‖ ^ 2 * ∑ i ∈ S, x i ^ 2 := by
      rw [dotProduct_projection_mulVec_self]

end YangMills.RG
