/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98SourceFieldScale
import YangMills.RG.OrderedExponentialQuadraticBound

/-!
# The quadratic source budget for the CMP98 four-contour generator word

This is the first quantitative specialization of the generic ordered-word
estimate to the literal four contours in CMP98 (121).  Every generator is
produced from the physical cochain, and the final endpoint replaces the
word length by the volume-independent source bound `2 * (d + 1) * M`.

The word here records the generator/exponential budget.  Identifying its
background-conjugated form with the complete physical four-holonomy is the
next source bridge; this file does not assert that identity prematurely.
-/

namespace YangMills.RG

open YangMills
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp98SourceGeneratorWordMatrixL2NormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

/-- Ordered matrix generators carried by the literal four-contour word. -/
def cmp98SourceFourContourGenerators
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) :
    List (Matrix (Fin Nc) (Fin Nc) ℂ) :=
  (cmp98SourceFourContourEdges (Nc := Nc) b x).map
    (orientedWilsonGenerator A)

@[simp] theorem cmp98SourceFourContourGenerators_length
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) :
    (cmp98SourceFourContourGenerators A b x).length =
      (cmp98SourceFourContourEdges (Nc := Nc) b x).length := by
  simp [cmp98SourceFourContourGenerators]

/-- Every member of the physical generator word obeys the same source sup
bound. -/
theorem norm_of_mem_cmp98SourceFourContourGenerators_le
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (X : Matrix (Fin Nc) (Fin Nc) ℂ)
    (hX : X ∈ cmp98SourceFourContourGenerators A b x) :
    ‖X‖ ≤ cmp98SourceFieldSupNorm A := by
  rcases List.mem_map.mp hX with ⟨e, he, rfl⟩
  exact norm_generator_of_mem_cmp98SourceFourContourEdges_le A b x e he

/-- Exact-length quadratic estimate for the literal generator word. -/
theorem norm_cmp98SourceFourContourOrderedExp_sub_linear_le
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) (t : ℝ)
    (hsmall : |t| * cmp98SourceFieldSupNorm A ≤ 1 / 2) :
    let generators := cmp98SourceFourContourGenerators A b x
    ‖orderedExpProduct t generators - 1 - t • generators.sum‖ ≤
      (generators.length : ℝ) ^ 2 *
          (2 * (|t| * cmp98SourceFieldSupNorm A)) ^ 2 *
          (1 + 2 * (|t| * cmp98SourceFieldSupNorm A)) ^ generators.length +
        generators.length *
          (2 * (|t| * cmp98SourceFieldSupNorm A) ^ 2) := by
  dsimp only
  exact norm_orderedExpProduct_sub_one_sub_smul_sum_le
    t (cmp98SourceFieldSupNorm A) _
      (cmp98SourceFieldSupNorm_nonneg A)
      (norm_of_mem_cmp98SourceFourContourGenerators_le A b x) hsmall

/-- Source-scale form of the same estimate.  The complete right-hand side
depends on the block scale `M` and the field sup norm, but not on `N'`. -/
theorem norm_cmp98SourceFourContourOrderedExp_sub_linear_le_sourceScale
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (hx : x ∈ blockOf M N' b.1) (t : ℝ)
    (hsmall : |t| * cmp98SourceFieldSupNorm A ≤ 1 / 2) :
    let generators := cmp98SourceFourContourGenerators A b x
    let sourceLength : ℕ := 2 * (d + 1) * M
    ‖orderedExpProduct t generators - 1 - t • generators.sum‖ ≤
      (sourceLength : ℝ) ^ 2 *
          (2 * (|t| * cmp98SourceFieldSupNorm A)) ^ 2 *
          (1 + 2 * (|t| * cmp98SourceFieldSupNorm A)) ^ sourceLength +
        sourceLength *
          (2 * (|t| * cmp98SourceFieldSupNorm A) ^ 2) := by
  dsimp only
  let generators := cmp98SourceFourContourGenerators A b x
  let sourceLength : ℕ := 2 * (d + 1) * M
  let q : ℝ := |t| * cmp98SourceFieldSupNorm A
  have hraw := norm_cmp98SourceFourContourOrderedExp_sub_linear_le
    A b x t hsmall
  have hlen : generators.length ≤ sourceLength := by
    simpa [generators, sourceLength] using
      cmp98SourceFourContourEdges_length_le (Nc := Nc) b x hx
  have hcast : (generators.length : ℝ) ≤ sourceLength := by
    exact_mod_cast hlen
  have hbase : 1 ≤ 1 + 2 * q := by
    have hq : 0 ≤ q :=
      mul_nonneg (abs_nonneg t) (cmp98SourceFieldSupNorm_nonneg A)
    linarith
  have hpow : (1 + 2 * q) ^ generators.length ≤
      (1 + 2 * q) ^ sourceLength :=
    pow_le_pow_right₀ hbase hlen
  dsimp only [generators, q, sourceLength] at hraw ⊢
  refine hraw.trans (add_le_add ?_ ?_)
  · have hsq : (generators.length : ℝ) ^ 2 ≤
        (sourceLength : ℝ) ^ 2 := by
      exact sq_le_sq₀ (by positivity) (by positivity) |>.2 hcast
    have hfactor : 0 ≤ (2 * (|t| * cmp98SourceFieldSupNorm A)) ^ 2 :=
      sq_nonneg _
    calc
      (generators.length : ℝ) ^ 2 *
            (2 * (|t| * cmp98SourceFieldSupNorm A)) ^ 2 *
            (1 + 2 * (|t| * cmp98SourceFieldSupNorm A)) ^ generators.length
          ≤ (sourceLength : ℝ) ^ 2 *
            (2 * (|t| * cmp98SourceFieldSupNorm A)) ^ 2 *
            (1 + 2 * (|t| * cmp98SourceFieldSupNorm A)) ^ generators.length := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hsq hfactor)
                (pow_nonneg (by linarith [hbase]) generators.length)
      _ ≤ (sourceLength : ℝ) ^ 2 *
            (2 * (|t| * cmp98SourceFieldSupNorm A)) ^ 2 *
            (1 + 2 * (|t| * cmp98SourceFieldSupNorm A)) ^ sourceLength := by
              exact mul_le_mul_of_nonneg_left hpow
                (mul_nonneg (sq_nonneg _) hfactor)
  · exact mul_le_mul_of_nonneg_right hcast
      (mul_nonneg (by positivity) (sq_nonneg _))

end

end YangMills.RG
