/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98SourceNearLogDomain

/-!
# The source-explicit coarse-contour remainder in CMP98 (123)

The straight coarse bond in the represented block has exactly `M` fine
edges.  This file right-trivializes its literal physical holonomy, identifies
the genuine first variation with the transported generator sum, and consumes
the ordered exponential estimate at that exact source length.  Both the
displacement and the quadratic remainder are then transported back through
the unitary background word without loss.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp98CoarseContourQuadraticMatrixL2NormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

/-- Exact source-length displacement budget for the straight coarse path. -/
def cmp98SourceCoarseContourDisplacementBudget
    (A : PhysicalGaugeOneCochain d (M * N') Nc) (t : ℝ) : ℝ :=
  (M : ℝ) * (2 * (|t| * cmp98SourceFieldSupNorm A)) *
    (1 + 2 * (|t| * cmp98SourceFieldSupNorm A)) ^ M

/-- Exact source-length quadratic budget for the straight coarse path. -/
def cmp98SourceCoarseContourQuadraticBudget
    (A : PhysicalGaugeOneCochain d (M * N') Nc) (t : ℝ) : ℝ :=
  (M : ℝ) ^ 2 * (2 * (|t| * cmp98SourceFieldSupNorm A)) ^ 2 *
      (1 + 2 * (|t| * cmp98SourceFieldSupNorm A)) ^ M +
    (M : ℝ) * (2 * (|t| * cmp98SourceFieldSupNorm A) ^ 2)

theorem cmp98SourceCoarseContourDisplacementBudget_nonneg
    (A : PhysicalGaugeOneCochain d (M * N') Nc) (t : ℝ) :
    0 ≤ cmp98SourceCoarseContourDisplacementBudget A t := by
  unfold cmp98SourceCoarseContourDisplacementBudget
  have hq : 0 ≤ |t| * cmp98SourceFieldSupNorm A :=
    mul_nonneg (abs_nonneg t) (cmp98SourceFieldSupNorm_nonneg A)
  positivity

theorem cmp98SourceCoarseContourQuadraticBudget_nonneg
    (A : PhysicalGaugeOneCochain d (M * N') Nc) (t : ℝ) :
    0 ≤ cmp98SourceCoarseContourQuadraticBudget A t := by
  unfold cmp98SourceCoarseContourQuadraticBudget
  have hq : 0 ≤ |t| * cmp98SourceFieldSupNorm A :=
    mul_nonneg (abs_nonneg t) (cmp98SourceFieldSupNorm_nonneg A)
  positivity

/-- For an arbitrary physical contour, the derivative of its right-
trivialized curve is exactly the sum of the prefix-transported generators. -/
theorem cmp98ContourFirstVariation_mul_backgroundConjTranspose_eq_generatorSum
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (es : List (ConcreteEdge d (M * N'))) :
    cmp98ContourFirstVariation U A es 0 *
        Matrix.conjTranspose (cmp98ContourMatrixCurve U A es 0) =
      (cmp98ContourTransportedGenerators U A es).sum := by
  have hleft := (hasDerivAt_cmp98ContourMatrixCurve U A es 0).mul_const
    (Matrix.conjTranspose (cmp98ContourMatrixCurve U A es 0))
  have hright : HasDerivAt
      (fun t => cmp98OrderedPhysicalExpProduct t
        (cmp98ContourTransportedGenerators U A es))
      (cmp98ContourTransportedGenerators U A es).sum 0 := by
    simpa [cmp98OrderedPhysicalExpProduct_eq_orderedExpProduct] using
      hasDerivAt_orderedExpProduct_zero
        (cmp98ContourTransportedGenerators U A es)
  have hfun :
      (fun t => cmp98ContourMatrixCurve U A es t *
        Matrix.conjTranspose (cmp98ContourMatrixCurve U A es 0)) =
      fun t => cmp98OrderedPhysicalExpProduct t
        (cmp98ContourTransportedGenerators U A es) := by
    funext t
    exact cmp98ContourMatrixCurve_mul_backgroundConjTranspose_eq_expProduct
      U A es t
  rw [hfun] at hleft
  exact hleft.unique hright

/-- Displacement of the right-trivialized straight coarse holonomy at the
literal source length `M`. -/
theorem norm_cmp98SourceCoarseRelativeContour_sub_one_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ)
    (hsmall : |t| * cmp98SourceFieldSupNorm A ≤ 1 / 2) :
    ‖cmp98ContourMatrixCurve U A
          (cmp98SourceCoarseBondPath (Nc := Nc) b) t *
        Matrix.conjTranspose (cmp98ContourMatrixCurve U A
          (cmp98SourceCoarseBondPath (Nc := Nc) b) 0) - 1‖ ≤
      cmp98SourceCoarseContourDisplacementBudget A t := by
  have hraw := norm_orderedExpProduct_sub_one_le
    t (cmp98SourceFieldSupNorm A)
      (cmp98ContourTransportedGenerators U A
        (cmp98SourceCoarseBondPath (Nc := Nc) b))
      (cmp98SourceFieldSupNorm_nonneg A)
      (fun X hX => norm_of_mem_cmp98PrefixTransportedGenerators_le
        U A 1 (cmp98SourceCoarseBondPath (Nc := Nc) b) X hX)
      hsmall
  rw [← cmp98OrderedPhysicalExpProduct_eq_orderedExpProduct,
    ← cmp98ContourMatrixCurve_mul_backgroundConjTranspose_eq_expProduct
      U A (cmp98SourceCoarseBondPath (Nc := Nc) b) t] at hraw
  simpa [cmp98SourceCoarseContourDisplacementBudget,
    cmp98SourceCoarseBondPath_length (Nc := Nc)] using hraw

/-- Quadratic remainder of the right-trivialized straight coarse holonomy,
with the genuine physical first variation as its linear term. -/
theorem norm_cmp98SourceCoarseRelativeContour_sub_one_sub_linear_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ)
    (hsmall : |t| * cmp98SourceFieldSupNorm A ≤ 1 / 2) :
    ‖cmp98ContourMatrixCurve U A
          (cmp98SourceCoarseBondPath (Nc := Nc) b) t *
        Matrix.conjTranspose (cmp98ContourMatrixCurve U A
          (cmp98SourceCoarseBondPath (Nc := Nc) b) 0) - 1 -
        t • (cmp98ContourFirstVariation U A
          (cmp98SourceCoarseBondPath (Nc := Nc) b) 0 *
          Matrix.conjTranspose (cmp98ContourMatrixCurve U A
            (cmp98SourceCoarseBondPath (Nc := Nc) b) 0))‖ ≤
      cmp98SourceCoarseContourQuadraticBudget A t := by
  have hraw := norm_orderedExpProduct_sub_one_sub_smul_sum_le
    t (cmp98SourceFieldSupNorm A)
      (cmp98ContourTransportedGenerators U A
        (cmp98SourceCoarseBondPath (Nc := Nc) b))
      (cmp98SourceFieldSupNorm_nonneg A)
      (fun X hX => norm_of_mem_cmp98PrefixTransportedGenerators_le
        U A 1 (cmp98SourceCoarseBondPath (Nc := Nc) b) X hX)
      hsmall
  rw [← cmp98OrderedPhysicalExpProduct_eq_orderedExpProduct,
    ← cmp98ContourMatrixCurve_mul_backgroundConjTranspose_eq_expProduct
      U A (cmp98SourceCoarseBondPath (Nc := Nc) b) t,
    ← cmp98ContourFirstVariation_mul_backgroundConjTranspose_eq_generatorSum
      U A (cmp98SourceCoarseBondPath (Nc := Nc) b)] at hraw
  simpa [cmp98SourceCoarseContourQuadraticBudget,
    cmp98SourceCoarseBondPath_length (Nc := Nc)] using hraw

/-- Unnormalized displacement of the literal straight coarse holonomy. -/
theorem norm_cmp98SourceCoarseContour_sub_zero_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ)
    (hsmall : |t| * cmp98SourceFieldSupNorm A ≤ 1 / 2) :
    ‖cmp98ContourMatrixCurve U A
          (cmp98SourceCoarseBondPath (Nc := Nc) b) t -
        cmp98ContourMatrixCurve U A
          (cmp98SourceCoarseBondPath (Nc := Nc) b) 0‖ ≤
      cmp98SourceCoarseContourDisplacementBudget A t := by
  let es := cmp98SourceCoarseBondPath (Nc := Nc) (M := M) b
  let Ct := cmp98ContourMatrixCurve U A es t
  let C0 := cmp98ContourMatrixCurve U A es 0
  have hunit : Matrix.conjTranspose C0 * C0 = 1 := by
    exact cmp98ContourMatrixCurve_conjTranspose_mul_general U A es 0
  have hdecomp : Ct - C0 = (Ct * Matrix.conjTranspose C0 - 1) * C0 := by
    rw [sub_mul, one_mul, mul_assoc, hunit, mul_one]
  have hnorm0 : ‖C0‖ = 1 := by
    dsimp only [C0]
    rw [cmp98ContourMatrixCurve_zero_eq_wilsonLine]
    exact norm_SUN_coe_l2_opNorm _
  rw [hdecomp]
  calc
    ‖(Ct * Matrix.conjTranspose C0 - 1) * C0‖
        ≤ ‖Ct * Matrix.conjTranspose C0 - 1‖ * ‖C0‖ := norm_mul_le _ _
    _ = ‖Ct * Matrix.conjTranspose C0 - 1‖ := by rw [hnorm0, mul_one]
    _ ≤ _ := by
      simpa [es, Ct, C0] using
        norm_cmp98SourceCoarseRelativeContour_sub_one_le U A b t hsmall

/-- Unnormalized quadratic remainder of the literal straight coarse
holonomy.  Unitary transport introduces no loss. -/
theorem norm_cmp98SourceCoarseContour_sub_zero_sub_linear_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ)
    (hsmall : |t| * cmp98SourceFieldSupNorm A ≤ 1 / 2) :
    ‖cmp98ContourMatrixCurve U A
          (cmp98SourceCoarseBondPath (Nc := Nc) b) t -
        cmp98ContourMatrixCurve U A
          (cmp98SourceCoarseBondPath (Nc := Nc) b) 0 -
        t • cmp98ContourFirstVariation U A
          (cmp98SourceCoarseBondPath (Nc := Nc) b) 0‖ ≤
      cmp98SourceCoarseContourQuadraticBudget A t := by
  let es := cmp98SourceCoarseBondPath (Nc := Nc) (M := M) b
  let Ct := cmp98ContourMatrixCurve U A es t
  let C0 := cmp98ContourMatrixCurve U A es 0
  let Cp := cmp98ContourFirstVariation U A es 0
  have hunit : Matrix.conjTranspose C0 * C0 = 1 := by
    exact cmp98ContourMatrixCurve_conjTranspose_mul_general U A es 0
  have hbase : (Ct * Matrix.conjTranspose C0 - 1) * C0 = Ct - C0 := by
    rw [sub_mul, one_mul, mul_assoc, hunit, mul_one]
  have hlinear : (t • (Cp * Matrix.conjTranspose C0)) * C0 = t • Cp := by
    rw [smul_mul_assoc, mul_assoc, hunit, mul_one]
  have hdecomp : Ct - C0 - t • Cp =
      (Ct * Matrix.conjTranspose C0 - 1 -
        t • (Cp * Matrix.conjTranspose C0)) * C0 := by
    calc
      Ct - C0 - t • Cp =
          (Ct * Matrix.conjTranspose C0 - 1) * C0 -
            (t • (Cp * Matrix.conjTranspose C0)) * C0 := by
              rw [hbase, hlinear]
      _ = _ := by noncomm_ring
  have hnorm0 : ‖C0‖ = 1 := by
    dsimp only [C0]
    rw [cmp98ContourMatrixCurve_zero_eq_wilsonLine]
    exact norm_SUN_coe_l2_opNorm _
  have hrelative :=
    norm_cmp98SourceCoarseRelativeContour_sub_one_sub_linear_le
      U A b t hsmall
  rw [hdecomp]
  calc
    ‖(Ct * Matrix.conjTranspose C0 - 1 -
          t • (Cp * Matrix.conjTranspose C0)) * C0‖
        ≤ ‖Ct * Matrix.conjTranspose C0 - 1 -
            t • (Cp * Matrix.conjTranspose C0)‖ * ‖C0‖ := norm_mul_le _ _
    _ = ‖Ct * Matrix.conjTranspose C0 - 1 -
            t • (Cp * Matrix.conjTranspose C0)‖ := by rw [hnorm0, mul_one]
    _ ≤ _ := by simpa [es, Ct, C0, Cp] using hrelative

end

end YangMills.RG
