/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214ConditionedOuterCarrier
import YangMills.RG.BalabanCMP116ComplexQuadraticSchur
import YangMills.RG.BalabanCMP116FiniteCarrierLinftyNorm

/-!
# Bilateral and trace control after conditioning the outer carrier

The coordinate projection has `l∞` operator norm at most one.  Consequently
compressing `R1` to `P_Zᵀ R1 P_Z` cannot enlarge either bilateral norm or the
symmetric trace-multiplier budget.
-/

namespace YangMills.RG

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator

namespace CMP116Eq214PhysicalContourDensity

/-- The conditioned complex projection is the standard finite-carrier
projection used by the determinant factorization. -/
theorem conditionedOuterProjection_eq_finsetCoordinateProjection
    {Bond : Type*} {lieDim : ℕ}
    [Fintype Bond] [DecidableEq Bond]
    (S : Finset (Bond × Fin lieDim)) :
    conditionedOuterProjection S =
      cmp116FinsetCoordinateProjection (α := ℂ) S := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i ∈ S
    · simp [conditionedOuterProjection, cmp116Eq223CoordinateProjection,
        cmp116FinsetCoordinateProjection, Matrix.diagonal, hi]
    · simp [conditionedOuterProjection, cmp116Eq223CoordinateProjection,
        cmp116FinsetCoordinateProjection, Matrix.diagonal, hi]
  · simp [conditionedOuterProjection, cmp116Eq223CoordinateProjection,
      cmp116FinsetCoordinateProjection, Matrix.diagonal, hij]

/-- The complex coordinate projection has `l∞` operator norm at most one. -/
theorem linfty_opNorm_conditionedOuterProjection_le_one
    {Bond : Type*} {lieDim : ℕ}
    [Fintype Bond] [DecidableEq Bond] [Nonempty (Bond × Fin lieDim)]
    (S : Finset (Bond × Fin lieDim)) :
    ‖conditionedOuterProjection S‖ ≤ 1 := by
  rw [conditionedOuterProjection_eq_finsetCoordinateProjection,
    ← cmp116FinsetColumnInclusion_mul_restriction]
  calc
    ‖cmp116FinsetColumnInclusion (α := ℂ) S *
        cmp116FinsetCoordinateRestriction (α := ℂ) S‖ ≤
      ‖cmp116FinsetColumnInclusion (α := ℂ) S‖ *
        ‖cmp116FinsetCoordinateRestriction (α := ℂ) S‖ :=
      Matrix.linfty_opNorm_mul _ _
    _ ≤ 1 * 1 := by
      gcongr
      exact linfty_opNorm_cmp116FinsetColumnInclusion_le_one S
      exact linfty_opNorm_cmp116FinsetCoordinateRestriction_le_one S
    _ = 1 := by ring

/-- Compression by the conditioned projection cannot enlarge the row norm. -/
theorem linfty_opNorm_conditionedOuterProjection_mul_mul_le
    {Bond : Type*} {lieDim : ℕ}
    [Fintype Bond] [DecidableEq Bond] [Nonempty (Bond × Fin lieDim)]
    (S : Finset (Bond × Fin lieDim))
    (A : Matrix (Bond × Fin lieDim) (Bond × Fin lieDim) ℂ) :
    ‖conditionedOuterProjection S * A * conditionedOuterProjection S‖ ≤
      ‖A‖ := by
  calc
    ‖conditionedOuterProjection S * A * conditionedOuterProjection S‖ ≤
        ‖conditionedOuterProjection S‖ * ‖A‖ *
          ‖conditionedOuterProjection S‖ :=
      Matrix.linfty_opNorm_mul_three_le _ _ _
    _ ≤ 1 * ‖A‖ * 1 := by
      gcongr
      exact linfty_opNorm_conditionedOuterProjection_le_one S
      exact linfty_opNorm_conditionedOuterProjection_le_one S
    _ = ‖A‖ := by ring

/-- The same compression estimate for the transposed matrix. -/
theorem linfty_opNorm_transpose_conditionedOuterProjection_mul_mul_le
    {Bond : Type*} {lieDim : ℕ}
    [Fintype Bond] [DecidableEq Bond] [Nonempty (Bond × Fin lieDim)]
    (S : Finset (Bond × Fin lieDim))
    (A : Matrix (Bond × Fin lieDim) (Bond × Fin lieDim) ℂ) :
    ‖(conditionedOuterProjection S * A *
        conditionedOuterProjection S).transpose‖ ≤
      ‖A.transpose‖ := by
  simpa only [Matrix.transpose_mul, conditionedOuterProjection_transpose,
      Matrix.mul_assoc] using
    (linfty_opNorm_conditionedOuterProjection_mul_mul_le S A.transpose)

/-- Symmetry is preserved when a symmetric test matrix is compressed by the
conditioned coordinate projection. -/
theorem transpose_conditionedOuterProjection_mul_mul
    {Bond : Type*} {lieDim : ℕ}
    [Fintype Bond] [DecidableEq Bond]
    (S : Finset (Bond × Fin lieDim))
    (Q : Matrix (Bond × Fin lieDim) (Bond × Fin lieDim) ℂ)
    (hQ : Q.transpose = Q) :
    (conditionedOuterProjection S * Q *
        conditionedOuterProjection S).transpose =
      conditionedOuterProjection S * Q * conditionedOuterProjection S := by
  simpa only [Matrix.transpose_mul, conditionedOuterProjection_transpose,
      Matrix.mul_assoc, hQ]

/-- Cyclicity moves both carrier projections from `R1` to the symmetric test
matrix used by the near-log trace estimate. -/
theorem trace_conditionedOuterProjection_mul_mul_mul
    {Bond : Type*} {lieDim : ℕ}
    [Fintype Bond] [DecidableEq Bond]
    (S : Finset (Bond × Fin lieDim))
    (A Q : Matrix (Bond × Fin lieDim) (Bond × Fin lieDim) ℂ) :
    Matrix.trace
        ((conditionedOuterProjection S * A *
          conditionedOuterProjection S) * Q) =
      Matrix.trace
        (A * (conditionedOuterProjection S * Q *
          conditionedOuterProjection S)) := by
  calc
    Matrix.trace
        ((conditionedOuterProjection S * A *
          conditionedOuterProjection S) * Q) =
      Matrix.trace
        (conditionedOuterProjection S *
          (A * conditionedOuterProjection S * Q)) := by
            simp only [Matrix.mul_assoc]
    _ = Matrix.trace
        ((A * conditionedOuterProjection S * Q) *
          conditionedOuterProjection S) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace
        (A * (conditionedOuterProjection S * Q *
          conditionedOuterProjection S)) := by
            simp only [Matrix.mul_assoc]

/-- Any symmetric trace-multiplier estimate for `A` transfers unchanged to
its carrier compression. -/
theorem norm_trace_conditionedOuterProjection_mul_mul_le_of
    {Bond : Type*} {lieDim : ℕ}
    [Fintype Bond] [DecidableEq Bond] [Nonempty (Bond × Fin lieDim)]
    (S : Finset (Bond × Fin lieDim))
    (A : Matrix (Bond × Fin lieDim) (Bond × Fin lieDim) ℂ)
    {L : ℝ} (hL : 0 ≤ L)
    (htrace : ∀ Q : Matrix (Bond × Fin lieDim) (Bond × Fin lieDim) ℂ,
      Q.transpose = Q →
      ‖Matrix.trace (A * Q)‖ ≤ L * ‖Q‖)
    (Q : Matrix (Bond × Fin lieDim) (Bond × Fin lieDim) ℂ)
    (hQ : Q.transpose = Q) :
    ‖Matrix.trace
      ((conditionedOuterProjection S * A *
        conditionedOuterProjection S) * Q)‖ ≤ L * ‖Q‖ := by
  rw [trace_conditionedOuterProjection_mul_mul_mul]
  calc
    ‖Matrix.trace
        (A * (conditionedOuterProjection S * Q *
          conditionedOuterProjection S))‖ ≤
      L * ‖conditionedOuterProjection S * Q *
        conditionedOuterProjection S‖ :=
      htrace _ (transpose_conditionedOuterProjection_mul_mul S Q hQ)
    _ ≤ L * ‖Q‖ := by
      gcongr
      exact linfty_opNorm_conditionedOuterProjection_mul_mul_le S Q

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
