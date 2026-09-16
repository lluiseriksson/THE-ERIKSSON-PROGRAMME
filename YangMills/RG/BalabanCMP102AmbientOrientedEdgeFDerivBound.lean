/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116WilsonBackgroundFactorBounds
import YangMills.RG.NoncommutativeExpLipschitz

/-!
# Quantitative ambient derivative of one oriented Wilson edge

This module differentiates the literal ambient factor `exp(Z_b) U_b`.
For the reverse orientation it differentiates the conjugate transpose of
the same positive-bond factor.  The first derivative and its two-field
variation are controlled directly by the audited exponential derivative
budgets, with no edge-level Lipschitz constant supplied by the caller.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

local instance cmp102AmbientEdgeMatrixNormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

/-- Evaluation of one ambient bond coordinate is contractive for the
repository's product norm. -/
theorem norm_physicalAmbientMatrixTangent_apply_le
    (Z : PhysicalAmbientMatrixTangent d N Nc) (b : PhysicalBond d N) :
    ‖Z b‖ ≤ ‖Z‖ := by
  exact norm_le_pi_norm Z b

/-- Exact derivative of the matrix exponential after one bond evaluation. -/
theorem fderiv_physicalMatrixExp_eval_apply
    (Z H : PhysicalAmbientMatrixTangent d N Nc) (b : PhysicalBond d N) :
    fderiv ℝ (fun W : PhysicalAmbientMatrixTangent d N Nc =>
        physicalMatrixExp (W b)) Z H =
      fderiv ℝ
        (NormedSpace.exp :
          Matrix (Fin Nc) (Fin Nc) ℂ → Matrix (Fin Nc) (Fin Nc) ℂ)
        (Z b) (H b) := by
  letI : IsTopologicalRing (Matrix (Fin Nc) (Fin Nc) ℂ) :=
    physicalMatrixTopologicalRing Nc
  have hcomp :=
    (NormedSpace.exp_analytic (Z b)).differentiableAt.hasFDerivAt.comp Z
      (physicalAmbientBondEvalCLM b).hasFDerivAt
  have hApply := congrArg
    (fun L : PhysicalAmbientMatrixTangent d N Nc →L[ℝ]
      Matrix (Fin Nc) (Fin Nc) ℂ => L H) hcomp.fderiv
  simpa only [physicalMatrixExp, Function.comp_apply,
    ContinuousLinearMap.comp_apply] using hApply

/-- Exact derivative of the positive ambient link factor. -/
theorem fderiv_ambientPositiveBondMatrix_apply
    (U : PhysicalGaugeBackground d N Nc)
    (Z H : PhysicalAmbientMatrixTangent d N Nc)
    (b : PhysicalBond d N) :
    fderiv ℝ (fun W => ambientPositiveBondMatrix U W b) Z H =
      fderiv ℝ
          (NormedSpace.exp :
            Matrix (Fin Nc) (Fin Nc) ℂ → Matrix (Fin Nc) (Fin Nc) ℂ)
          (Z b) (H b) *
        (U (positiveEdgeOfPhysicalBond b)).val := by
  letI : IsTopologicalRing (Matrix (Fin Nc) (Fin Nc) ℂ) :=
    physicalMatrixTopologicalRing Nc
  have hExp :=
    (analyticAt_physicalMatrixExp_eval Z b).differentiableAt
  have hApply := congrArg
    (fun L : PhysicalAmbientMatrixTangent d N Nc →L[ℝ]
      Matrix (Fin Nc) (Fin Nc) ℂ => L H)
    (fderiv_mul_const' hExp (U (positiveEdgeOfPhysicalBond b)).val)
  calc
    _ = (MulOpposite.op (U (positiveEdgeOfPhysicalBond b)).val •
        fderiv ℝ (fun W : PhysicalAmbientMatrixTangent d N Nc =>
          physicalMatrixExp (W b)) Z) H := by
      simpa only [ambientPositiveBondMatrix] using hApply
    _ = _ := by
      rw [ContinuousLinearMap.smul_apply, op_smul_eq_mul,
        fderiv_physicalMatrixExp_eval_apply Z H b]

/-- Ordered derivative value for either orientation of one physical edge. -/
def cmp102AmbientOrientedEdgeDerivative
    (U : PhysicalGaugeBackground d N Nc)
    (Z H : PhysicalAmbientMatrixTangent d N Nc)
    (e : ConcreteEdge d N) : Matrix (Fin Nc) (Fin Nc) ℂ :=
  let D :=
    fderiv ℝ
        (NormedSpace.exp :
          Matrix (Fin Nc) (Fin Nc) ℂ → Matrix (Fin Nc) (Fin Nc) ℂ)
        (Z (physicalBondOfEdge e)) (H (physicalBondOfEdge e)) *
      orientedWilsonPositiveBase U e
  if e.sign then D else Dᴴ

/-- The bundled ambient derivative is literally the ordered derivative
defined above, including the reverse-orientation adjoint. -/
theorem fderiv_ambientOrientedEdgeMatrix_apply
    (U : PhysicalGaugeBackground d N Nc)
    (Z H : PhysicalAmbientMatrixTangent d N Nc)
    (e : ConcreteEdge d N) :
    fderiv ℝ (fun W => ambientOrientedEdgeMatrix U W e) Z H =
      cmp102AmbientOrientedEdgeDerivative U Z H e := by
  let b := physicalBondOfEdge e
  by_cases h : e.sign
  · simp [ambientOrientedEdgeMatrix, cmp102AmbientOrientedEdgeDerivative, h]
    exact fderiv_ambientPositiveBondMatrix_apply U Z H b
  · have hs : e.sign = false := Bool.eq_false_of_not_eq_true h
    simp [cmp102AmbientOrientedEdgeDerivative, hs]
    rw [show
      (fun W : PhysicalAmbientMatrixTangent d N Nc =>
        ambientOrientedEdgeMatrix U W e) =
        (matrixConjTransposeCLM (Nc := Nc)) ∘
          (fun W : PhysicalAmbientMatrixTangent d N Nc =>
            ambientPositiveBondMatrix U W b) by
      funext W
      simp [ambientOrientedEdgeMatrix, hs, Function.comp_apply,
        matrixConjTransposeCLM_apply, b]]
    have hPos :=
      (analyticAt_ambientPositiveBondMatrix U Z b).differentiableAt.hasFDerivAt
    have hStar :=
      (matrixConjTransposeCLM (Nc := Nc)).hasFDerivAt.comp Z hPos
    have hApply := congrArg
      (fun L : PhysicalAmbientMatrixTangent d N Nc →L[ℝ]
        Matrix (Fin Nc) (Fin Nc) ℂ => L H) hStar.fderiv
    calc
      _ = matrixConjTransposeCLM
          ((fderiv ℝ
            (fun W : PhysicalAmbientMatrixTangent d N Nc =>
              ambientPositiveBondMatrix U W b) Z) H) := by
        simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply]
          using hApply
      _ = _ := by
        rw [fderiv_ambientPositiveBondMatrix_apply U Z H b]
        simp [matrixConjTransposeCLM_apply, Matrix.conjTranspose_mul,
          orientedWilsonPositiveBase, b]

/-- First derivative of one oriented ambient factor on a radius-`r` ball. -/
theorem norm_fderiv_ambientOrientedEdgeMatrix_le
    (U : PhysicalGaugeBackground d N Nc)
    (Z : PhysicalAmbientMatrixTangent d N Nc)
    (e : ConcreteEdge d N) {r : ℝ}
    (hZ : ‖Z (physicalBondOfEdge e)‖ ≤ r) :
    ‖fderiv ℝ (fun W => ambientOrientedEdgeMatrix U W e) Z‖ ≤
      expDerivativeBudget r := by
  have hbudget0 : 0 ≤ expDerivativeBudget r :=
    (norm_nonneg
      (fderiv ℝ
        (NormedSpace.exp :
          Matrix (Fin Nc) (Fin Nc) ℂ → Matrix (Fin Nc) (Fin Nc) ℂ)
        (Z (physicalBondOfEdge e)))).trans
      (norm_fderiv_exp_le_derivativeBudget hZ)
  apply ContinuousLinearMap.opNorm_le_bound
    (fderiv ℝ (fun W => ambientOrientedEdgeMatrix U W e) Z)
    hbudget0
  intro H
  change
    ‖(fderiv ℝ
      (fun W : PhysicalAmbientMatrixTangent d N Nc =>
        ambientOrientedEdgeMatrix U W e) Z) H‖ ≤
      expDerivativeBudget r * ‖H‖
  rw [fderiv_ambientOrientedEdgeMatrix_apply U Z H e]
  unfold cmp102AmbientOrientedEdgeDerivative
  split
  · calc
      ‖fderiv ℝ
            (NormedSpace.exp :
              Matrix (Fin Nc) (Fin Nc) ℂ →
                Matrix (Fin Nc) (Fin Nc) ℂ)
            (Z (physicalBondOfEdge e)) (H (physicalBondOfEdge e)) *
          orientedWilsonPositiveBase U e‖
          ≤ ‖fderiv ℝ
                (NormedSpace.exp :
                  Matrix (Fin Nc) (Fin Nc) ℂ →
                    Matrix (Fin Nc) (Fin Nc) ℂ)
                (Z (physicalBondOfEdge e))
                (H (physicalBondOfEdge e))‖ *
              ‖orientedWilsonPositiveBase U e‖ := norm_mul_le _ _
      _ ≤ expDerivativeBudget r * ‖H (physicalBondOfEdge e)‖ := by
        rw [norm_orientedWilsonPositiveBase, mul_one]
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right
            (norm_fderiv_exp_le_derivativeBudget hZ)
            (norm_nonneg _))
      _ ≤ expDerivativeBudget r * ‖H‖ :=
        mul_le_mul_of_nonneg_left
          (norm_physicalAmbientMatrixTangent_apply_le H
            (physicalBondOfEdge e)) hbudget0
  · rw [Matrix.l2_opNorm_conjTranspose]
    calc
      ‖fderiv ℝ
            (NormedSpace.exp :
              Matrix (Fin Nc) (Fin Nc) ℂ →
                Matrix (Fin Nc) (Fin Nc) ℂ)
            (Z (physicalBondOfEdge e)) (H (physicalBondOfEdge e)) *
          orientedWilsonPositiveBase U e‖
          ≤ ‖fderiv ℝ
                (NormedSpace.exp :
                  Matrix (Fin Nc) (Fin Nc) ℂ →
                    Matrix (Fin Nc) (Fin Nc) ℂ)
                (Z (physicalBondOfEdge e))
                (H (physicalBondOfEdge e))‖ *
              ‖orientedWilsonPositiveBase U e‖ := norm_mul_le _ _
      _ ≤ expDerivativeBudget r * ‖H (physicalBondOfEdge e)‖ := by
        rw [norm_orientedWilsonPositiveBase, mul_one]
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right
            (norm_fderiv_exp_le_derivativeBudget hZ)
            (norm_nonneg _))
      _ ≤ expDerivativeBudget r * ‖H‖ :=
        mul_le_mul_of_nonneg_left
          (norm_physicalAmbientMatrixTangent_apply_le H
            (physicalBondOfEdge e)) hbudget0

/-- Lipschitz variation of the derivative of one oriented ambient factor.
The constant is the genuine exponential second-derivative budget. -/
theorem norm_fderiv_ambientOrientedEdgeMatrix_sub_le
    (U : PhysicalGaugeBackground d N Nc)
    (Z W : PhysicalAmbientMatrixTangent d N Nc)
    (e : ConcreteEdge d N) {r : ℝ}
    (hZ : ‖Z (physicalBondOfEdge e)‖ ≤ r)
    (hW : ‖W (physicalBondOfEdge e)‖ ≤ r) :
    ‖fderiv ℝ (fun V => ambientOrientedEdgeMatrix U V e) Z -
        fderiv ℝ (fun V => ambientOrientedEdgeMatrix U V e) W‖ ≤
      expSecondDerivativeBudget r * ‖Z - W‖ := by
  have hbudget0 : 0 ≤ expSecondDerivativeBudget r :=
    expSecondDerivativeBudget_nonneg r ((norm_nonneg _).trans hZ)
  apply ContinuousLinearMap.opNorm_le_bound
    (fderiv ℝ (fun V => ambientOrientedEdgeMatrix U V e) Z -
      fderiv ℝ (fun V => ambientOrientedEdgeMatrix U V e) W)
    (mul_nonneg hbudget0 (norm_nonneg (Z - W)))
  intro H
  change
    ‖((fderiv ℝ
        (fun V : PhysicalAmbientMatrixTangent d N Nc =>
          ambientOrientedEdgeMatrix U V e) Z -
      fderiv ℝ
        (fun V : PhysicalAmbientMatrixTangent d N Nc =>
          ambientOrientedEdgeMatrix U V e) W) H)‖ ≤
      (expSecondDerivativeBudget r * ‖Z - W‖) * ‖H‖
  rw [ContinuousLinearMap.sub_apply,
    fderiv_ambientOrientedEdgeMatrix_apply U Z H e,
    fderiv_ambientOrientedEdgeMatrix_apply U W H e]
  unfold cmp102AmbientOrientedEdgeDerivative
  split
  · rw [← sub_mul]
    calc
      ‖(fderiv ℝ
              (NormedSpace.exp :
                Matrix (Fin Nc) (Fin Nc) ℂ →
                  Matrix (Fin Nc) (Fin Nc) ℂ)
              (Z (physicalBondOfEdge e)) -
            fderiv ℝ
              (NormedSpace.exp :
                Matrix (Fin Nc) (Fin Nc) ℂ →
                  Matrix (Fin Nc) (Fin Nc) ℂ)
              (W (physicalBondOfEdge e)))
            (H (physicalBondOfEdge e)) *
          orientedWilsonPositiveBase U e‖
          ≤ ‖(fderiv ℝ
                  (NormedSpace.exp :
                    Matrix (Fin Nc) (Fin Nc) ℂ →
                      Matrix (Fin Nc) (Fin Nc) ℂ)
                  (Z (physicalBondOfEdge e)) -
                fderiv ℝ
                  (NormedSpace.exp :
                    Matrix (Fin Nc) (Fin Nc) ℂ →
                      Matrix (Fin Nc) (Fin Nc) ℂ)
                  (W (physicalBondOfEdge e)))
                (H (physicalBondOfEdge e))‖ := by
        simpa [norm_orientedWilsonPositiveBase] using
          (norm_mul_le
            ((fderiv ℝ
                (NormedSpace.exp :
                  Matrix (Fin Nc) (Fin Nc) ℂ →
                    Matrix (Fin Nc) (Fin Nc) ℂ)
                (Z (physicalBondOfEdge e)) -
              fderiv ℝ
                (NormedSpace.exp :
                  Matrix (Fin Nc) (Fin Nc) ℂ →
                    Matrix (Fin Nc) (Fin Nc) ℂ)
                (W (physicalBondOfEdge e)))
              (H (physicalBondOfEdge e)))
            (orientedWilsonPositiveBase U e))
      _ ≤
          (expSecondDerivativeBudget r *
            ‖Z (physicalBondOfEdge e) - W (physicalBondOfEdge e)‖) *
              ‖H (physicalBondOfEdge e)‖ :=
        (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right
            (norm_fderiv_exp_sub_le_secondDerivativeBudget hZ hW)
            (norm_nonneg _))
      _ ≤ (expSecondDerivativeBudget r * ‖Z - W‖) * ‖H‖ := by
        gcongr
        · exact norm_physicalAmbientMatrixTangent_apply_le
            (Z - W) (physicalBondOfEdge e)
        · exact norm_physicalAmbientMatrixTangent_apply_le
            H (physicalBondOfEdge e)
  · rw [← Matrix.conjTranspose_sub,
      Matrix.l2_opNorm_conjTranspose, ← sub_mul]
    calc
      ‖(fderiv ℝ
              (NormedSpace.exp :
                Matrix (Fin Nc) (Fin Nc) ℂ →
                  Matrix (Fin Nc) (Fin Nc) ℂ)
              (Z (physicalBondOfEdge e)) -
            fderiv ℝ
              (NormedSpace.exp :
                Matrix (Fin Nc) (Fin Nc) ℂ →
                  Matrix (Fin Nc) (Fin Nc) ℂ)
              (W (physicalBondOfEdge e)))
            (H (physicalBondOfEdge e)) *
          orientedWilsonPositiveBase U e‖
          ≤ ‖(fderiv ℝ
                  (NormedSpace.exp :
                    Matrix (Fin Nc) (Fin Nc) ℂ →
                      Matrix (Fin Nc) (Fin Nc) ℂ)
                  (Z (physicalBondOfEdge e)) -
                fderiv ℝ
                  (NormedSpace.exp :
                    Matrix (Fin Nc) (Fin Nc) ℂ →
                      Matrix (Fin Nc) (Fin Nc) ℂ)
                  (W (physicalBondOfEdge e)))
                (H (physicalBondOfEdge e))‖ := by
        simpa [norm_orientedWilsonPositiveBase] using
          (norm_mul_le
            ((fderiv ℝ
                (NormedSpace.exp :
                  Matrix (Fin Nc) (Fin Nc) ℂ →
                    Matrix (Fin Nc) (Fin Nc) ℂ)
                (Z (physicalBondOfEdge e)) -
              fderiv ℝ
                (NormedSpace.exp :
                  Matrix (Fin Nc) (Fin Nc) ℂ →
                    Matrix (Fin Nc) (Fin Nc) ℂ)
                (W (physicalBondOfEdge e)))
              (H (physicalBondOfEdge e)))
            (orientedWilsonPositiveBase U e))
      _ ≤
          (expSecondDerivativeBudget r *
            ‖Z (physicalBondOfEdge e) - W (physicalBondOfEdge e)‖) *
              ‖H (physicalBondOfEdge e)‖ :=
        (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right
            (norm_fderiv_exp_sub_le_secondDerivativeBudget hZ hW)
            (norm_nonneg _))
      _ ≤ (expSecondDerivativeBudget r * ‖Z - W‖) * ‖H‖ := by
        gcongr
        · exact norm_physicalAmbientMatrixTangent_apply_le
            (Z - W) (physicalBondOfEdge e)
        · exact norm_physicalAmbientMatrixTangent_apply_le
            H (physicalBondOfEdge e)

end

end YangMills.RG
