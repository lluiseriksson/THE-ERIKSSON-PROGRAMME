/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102AmbientOrientedEdgeThirdJetBound

/-!
# Physical third jets of ordered Wilson lines

The literal Wilson line is a noncommutative ordered product of physical
oriented edges.  This file propagates the source-generated edge jets through
that product by the quantitative bilinear Leibniz rule.  The resulting budget
depends on the contour length and edge radius, never on the ambient volume.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
  [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp102AmbientWilsonLineThirdJetMatrixNormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

local instance cmp102AmbientWilsonLineCMLSeminormed (n : ℕ) :
    SeminormedAddCommGroup
      (PhysicalAmbientMatrixTangent d (M * N') Nc [×n]→L[ℝ]
        Matrix (Fin Nc) (Fin Nc) ℂ) :=
  ContinuousMultilinearMap.seminormedAddCommGroup

/-- Matrix multiplication, regarded as a real continuous bilinear map, is
contractive for the matrix `L²` operator norm. -/
theorem norm_cmp102AmbientMatrixMulCLM_le_one :
    ‖ContinuousLinearMap.mul ℝ
        (Matrix (Fin Nc) (Fin Nc) ℂ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro B
  exact norm_mul_le A B

/-- A common budget for every derivative order at most three of an ordered
line of the specified length.  The factor eight is the sum of the binomial
coefficients in the worst allowed order. -/
def cmp102AmbientWilsonLineOrderThreeJetBudget
    (r : NNReal) : ℕ → ℝ
  | 0 => 1
  | n + 1 =>
      8 * cmp102AmbientEdgeOrderThreeJetBudget (Nc := Nc) r *
        cmp102AmbientWilsonLineOrderThreeJetBudget r n

theorem cmp102AmbientWilsonLineOrderThreeJetBudget_nonneg
    (r : NNReal) :
    ∀ n, 0 ≤
      cmp102AmbientWilsonLineOrderThreeJetBudget
        (Nc := Nc) r n := by
  intro n
  induction n with
  | zero =>
      simp [cmp102AmbientWilsonLineOrderThreeJetBudget]
  | succ n ih =>
      rw [cmp102AmbientWilsonLineOrderThreeJetBudget]
      exact mul_nonneg
        (mul_nonneg (by norm_num)
          ((cmp102AmbientEdgeValueBudget_nonneg r.2).trans
            (le_max_left _ _))) ih

set_option maxHeartbeats 1200000 in
/-- Every jet through order three of the literal ordered Wilson line is
controlled by the source-generated edge budget and the contour length. -/
theorem norm_iteratedFDeriv_cmp98AmbientWilsonLineMatrix_le_orderThreeBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc)
    (es : List (ConcreteEdge d (M * N'))) (r : NNReal)
    (hZ : ∀ e ∈ es, ‖Z (physicalBondOfEdge e)‖ < r)
    (i : ℕ) (hi : i ≤ 3) :
    ‖iteratedFDeriv ℝ i
        (fun W => cmp98AmbientWilsonLineMatrix U W es) Z‖ ≤
      cmp102AmbientWilsonLineOrderThreeJetBudget
        (Nc := Nc) r es.length := by
  induction es generalizing i with
  | nil =>
      have hfun :
          (fun W : PhysicalAmbientMatrixTangent d (M * N') Nc =>
            cmp98AmbientWilsonLineMatrix U W []) =
          (fun _ => (1 : Matrix (Fin Nc) (Fin Nc) ℂ)) := rfl
      rw [hfun]
      interval_cases i
      · calc
          ‖iteratedFDeriv ℝ 0
              (fun _ : PhysicalAmbientMatrixTangent d (M * N') Nc =>
                (1 : Matrix (Fin Nc) (Fin Nc) ℂ)) Z‖ =
              ‖(1 : Matrix (Fin Nc) (Fin Nc) ℂ)‖ :=
            norm_iteratedFDeriv_zero
          _ = 1 := norm_one
          _ ≤ cmp102AmbientWilsonLineOrderThreeJetBudget
                (Nc := Nc) r [].length := by
            simp [cmp102AmbientWilsonLineOrderThreeJetBudget]
      · rw [iteratedFDeriv_const_of_ne (by norm_num)]
        calc
          ‖(0 : (PhysicalAmbientMatrixTangent d (M * N') Nc [×1]→L[ℝ]
              Matrix (Fin Nc) (Fin Nc) ℂ))‖ = 0 := norm_zero
          _ ≤ 1 := zero_le_one
          _ = cmp102AmbientWilsonLineOrderThreeJetBudget
                (Nc := Nc) r [].length := by
            simp [cmp102AmbientWilsonLineOrderThreeJetBudget]
      · rw [iteratedFDeriv_const_of_ne (by norm_num)]
        calc
          ‖(0 : (PhysicalAmbientMatrixTangent d (M * N') Nc [×2]→L[ℝ]
              Matrix (Fin Nc) (Fin Nc) ℂ))‖ = 0 := norm_zero
          _ ≤ 1 := zero_le_one
          _ = cmp102AmbientWilsonLineOrderThreeJetBudget
                (Nc := Nc) r [].length := by
            simp [cmp102AmbientWilsonLineOrderThreeJetBudget]
      · rw [iteratedFDeriv_const_of_ne (by norm_num)]
        calc
          ‖(0 : (PhysicalAmbientMatrixTangent d (M * N') Nc [×3]→L[ℝ]
              Matrix (Fin Nc) (Fin Nc) ℂ))‖ = 0 := norm_zero
          _ ≤ 1 := zero_le_one
          _ = cmp102AmbientWilsonLineOrderThreeJetBudget
                (Nc := Nc) r [].length := by
            simp [cmp102AmbientWilsonLineOrderThreeJetBudget]
  | cons e es ih =>
      have hHead :
          ContDiff ℝ 3
            (fun W : PhysicalAmbientMatrixTangent d (M * N') Nc =>
              ambientOrientedEdgeMatrix U W e) :=
        contDiff_iff_contDiffAt.mpr fun W =>
          (analyticAt_ambientOrientedEdgeMatrix U W e).contDiffAt
      have hTail :
          ContDiff ℝ 3
            (fun W : PhysicalAmbientMatrixTangent d (M * N') Nc =>
              cmp98AmbientWilsonLineMatrix U W es) :=
        contDiff_iff_contDiffAt.mpr fun W =>
          (analyticAt_cmp98AmbientWilsonLineMatrix U W es).contDiffAt
      have hLeibniz :=
        ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_le_one
          (ContinuousLinearMap.mul ℝ
            (Matrix (Fin Nc) (Fin Nc) ℂ))
          hHead hTail Z (n := i)
          (WithTop.coe_le_coe.mpr
            (WithTop.coe_le_coe.mpr hi))
          (norm_cmp102AmbientMatrixMulCLM_le_one (Nc := Nc))
      change
        ‖iteratedFDeriv ℝ i
            (fun W =>
              ambientOrientedEdgeMatrix U W e *
                cmp98AmbientWilsonLineMatrix U W es) Z‖ ≤ _
      calc
        _ ≤ ∑ j ∈ Finset.range (i + 1),
              (i.choose j : ℝ) *
                ‖iteratedFDeriv ℝ j
                  (fun W =>
                    ambientOrientedEdgeMatrix U W e) Z‖ *
                ‖iteratedFDeriv ℝ (i - j)
                  (fun W =>
                    cmp98AmbientWilsonLineMatrix U W es) Z‖ :=
          hLeibniz
        _ ≤ ∑ j ∈ Finset.range (i + 1),
              (i.choose j : ℝ) *
                cmp102AmbientEdgeOrderThreeJetBudget
                  (Nc := Nc) r *
                cmp102AmbientWilsonLineOrderThreeJetBudget
                  (Nc := Nc) r es.length := by
          apply Finset.sum_le_sum
          intro j hj
          have hj3 : j ≤ 3 :=
            Nat.le_trans
              (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hi
          have hsub3 : i - j ≤ 3 :=
            Nat.le_trans (Nat.sub_le i j) hi
          have hEdge :=
            norm_iteratedFDeriv_ambientOrientedEdgeMatrix_le_orderThreeBudget
              U Z e r (hZ e (by simp)) j hj3
          have hTail :=
            ih (fun a ha => hZ a (by simp [ha]))
              (i - j) hsub3
          calc
            (i.choose j : ℝ) *
                  ‖iteratedFDeriv ℝ j
                    (fun W => ambientOrientedEdgeMatrix U W e) Z‖ *
                  ‖iteratedFDeriv ℝ (i - j)
                    (fun W =>
                      cmp98AmbientWilsonLineMatrix U W es) Z‖
                ≤ (i.choose j : ℝ) *
                    cmp102AmbientEdgeOrderThreeJetBudget
                      (Nc := Nc) r *
                    ‖iteratedFDeriv ℝ (i - j)
                      (fun W =>
                        cmp98AmbientWilsonLineMatrix U W es) Z‖ := by
                  exact mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hEdge
                      (Nat.cast_nonneg _)) (norm_nonneg _)
            _ ≤ (i.choose j : ℝ) *
                    cmp102AmbientEdgeOrderThreeJetBudget
                      (Nc := Nc) r *
                    cmp102AmbientWilsonLineOrderThreeJetBudget
                      (Nc := Nc) r es.length := by
                  exact mul_le_mul_of_nonneg_left hTail
                    (mul_nonneg (Nat.cast_nonneg _)
                      ((cmp102AmbientEdgeValueBudget_nonneg r.2).trans
                        (le_max_left _ _)))
        _ ≤
            8 * cmp102AmbientEdgeOrderThreeJetBudget
                (Nc := Nc) r *
              cmp102AmbientWilsonLineOrderThreeJetBudget
                (Nc := Nc) r es.length := by
          have hprod :
              0 ≤ cmp102AmbientEdgeOrderThreeJetBudget
                    (Nc := Nc) r *
                  cmp102AmbientWilsonLineOrderThreeJetBudget
                    (Nc := Nc) r es.length :=
            mul_nonneg
              ((cmp102AmbientEdgeValueBudget_nonneg r.2).trans
                (le_max_left _ _))
              (cmp102AmbientWilsonLineOrderThreeJetBudget_nonneg
                (Nc := Nc) r es.length)
          interval_cases i <;>
            norm_num [Finset.sum_range_succ] <;>
            nlinarith
        _ =
            cmp102AmbientWilsonLineOrderThreeJetBudget
              (Nc := Nc) r (e :: es).length := by
          simp only [List.length_cons,
            cmp102AmbientWilsonLineOrderThreeJetBudget]

end

end YangMills.RG
