/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalChartBudget
import YangMills.RG.BalabanCMP116WilsonOrientedEdgeMixed
import YangMills.RG.NoncommutativeExpLipschitz

/-!
# Two-field Lipschitz control for the physical CMP98 exponentials

A fixed-point construction for the CMP102 correction requires comparing the
correction at two different fine fields.  The first source-faithful layer is
the physical edge exponential.

This module proves:

* exact linearity of the signed oriented generator under subtraction;
* a volume-independent bound by the source sup norm of the field difference;
* an explicit Lipschitz bound for the two physical matrix exponentials on a
  common radius-`r` ball.

The Lipschitz constant is derived from the already audited first- and
second-derivative budgets of the noncommutative exponential.  No abstract
Lipschitz constant is supplied.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp102TwoFieldMatrixNormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

/-- Linear Lipschitz budget for the exponential on a radius-`r` ball. -/
def cmp102ExpLipschitzBudget (r : ℝ) : ℝ :=
  2 * r * expSecondDerivativeBudget r + expDerivativeBudget r

theorem cmp102ExpLipschitzBudget_nonneg (r : ℝ) (hr : 0 ≤ r) :
    0 ≤ cmp102ExpLipschitzBudget r := by
  unfold cmp102ExpLipschitzBudget
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg (by positivity) hr)
      (expSecondDerivativeBudget_nonneg r hr))
    (expDerivativeBudget_nonneg r hr)

/-- The existing quadratic two-point Taylor estimate yields a linear
Lipschitz estimate on a common closed ball. -/
theorem norm_exp_sub_exp_le_cmp102ExpLipschitzBudget
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] [NormOneClass A]
    {r : ℝ} (hr : 0 ≤ r) {Y Z : A}
    (hY : ‖Y‖ ≤ r) (hZ : ‖Z‖ ≤ r) :
    ‖NormedSpace.exp Y - NormedSpace.exp Z‖ ≤
      cmp102ExpLipschitzBudget r * ‖Y - Z‖ := by
  have hraw := norm_exp_sub_exp_le_derivativeBudgets hr hY hZ
  have hdiff : ‖Y - Z‖ ≤ 2 * r := by
    calc
      ‖Y - Z‖ ≤ ‖Y‖ + ‖Z‖ := norm_sub_le _ _
      _ ≤ r + r := add_le_add hY hZ
      _ = 2 * r := by ring
  have hsq : ‖Y - Z‖ ^ 2 ≤ (2 * r) * ‖Y - Z‖ := by
    nlinarith [norm_nonneg (Y - Z)]
  calc
    ‖NormedSpace.exp Y - NormedSpace.exp Z‖
        ≤ expSecondDerivativeBudget r * ‖Y - Z‖ ^ 2 +
            expDerivativeBudget r * ‖Y - Z‖ := hraw
    _ ≤ expSecondDerivativeBudget r * ((2 * r) * ‖Y - Z‖) +
          expDerivativeBudget r * ‖Y - Z‖ := by
      gcongr
      exact expSecondDerivativeBudget_nonneg r hr
    _ = cmp102ExpLipschitzBudget r * ‖Y - Z‖ := by
      unfold cmp102ExpLipschitzBudget
      ring

/-- Exact subtraction law for the signed physical oriented generator. -/
theorem orientedWilsonGenerator_sub
    (A B : PhysicalGaugeOneCochain d (M * N') Nc)
    (e : ConcreteEdge d (M * N')) :
    orientedWilsonGenerator (A - B) e =
      orientedWilsonGenerator A e - orientedWilsonGenerator B e := by
  unfold orientedWilsonGenerator flatOrientedSuMatrixTangent
  split
  · simp only [PiLp.sub_apply, map_sub]
    rfl
  · simp only [PiLp.sub_apply, map_sub]
    change -(_ - _) = -_ - -_
    abel

/-- The signed generator difference is controlled by the source sup norm of
the actual field difference, uniformly in the volume. -/
theorem norm_orientedWilsonGenerator_sub_le_sourceSupNorm
    (A B : PhysicalGaugeOneCochain d (M * N') Nc)
    (e : ConcreteEdge d (M * N')) :
    ‖orientedWilsonGenerator A e - orientedWilsonGenerator B e‖ ≤
      cmp98SourceFieldSupNorm (A - B) := by
  rw [← orientedWilsonGenerator_sub]
  exact norm_orientedWilsonGenerator_le_cmp98SourceFieldSupNorm (A - B) e

/-- Source-explicit two-field Lipschitz estimate for one physical edge
exponential. -/
theorem norm_physicalMatrixExp_orientedGenerator_sub_le
    (A B : PhysicalGaugeOneCochain d (M * N') Nc)
    (e : ConcreteEdge d (M * N')) (t r : ℝ)
    (hr : 0 ≤ r)
    (hA : |t| * cmp98SourceFieldSupNorm A ≤ r)
    (hB : |t| * cmp98SourceFieldSupNorm B ≤ r) :
    ‖physicalMatrixExp (t • orientedWilsonGenerator A e) -
        physicalMatrixExp (t • orientedWilsonGenerator B e)‖ ≤
      cmp102ExpLipschitzBudget r *
        (|t| * cmp98SourceFieldSupNorm (A - B)) := by
  let YA := t • orientedWilsonGenerator A e
  let YB := t • orientedWilsonGenerator B e
  have hYA : ‖YA‖ ≤ r := by
    change ‖(t : ℂ) • orientedWilsonGenerator A e‖ ≤ r
    rw [norm_smul]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left
      (norm_orientedWilsonGenerator_le_cmp98SourceFieldSupNorm A e)
      (abs_nonneg t)).trans hA
  have hYB : ‖YB‖ ≤ r := by
    change ‖(t : ℂ) • orientedWilsonGenerator B e‖ ≤ r
    rw [norm_smul]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left
      (norm_orientedWilsonGenerator_le_cmp98SourceFieldSupNorm B e)
      (abs_nonneg t)).trans hB
  have hdiff :
      ‖YA - YB‖ ≤ |t| * cmp98SourceFieldSupNorm (A - B) := by
    change ‖t • orientedWilsonGenerator A e -
      t • orientedWilsonGenerator B e‖ ≤ _
    have hsmul :
        t • orientedWilsonGenerator A e -
            t • orientedWilsonGenerator B e =
          t • (orientedWilsonGenerator A e -
            orientedWilsonGenerator B e) := by
      module
    rw [hsmul]
    change ‖(t : ℂ) •
      (orientedWilsonGenerator A e - orientedWilsonGenerator B e)‖ ≤ _
    rw [norm_smul]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (norm_orientedWilsonGenerator_sub_le_sourceSupNorm A B e)
      (abs_nonneg t)
  have hexp :
      ‖NormedSpace.exp YA - NormedSpace.exp YB‖ ≤
        cmp102ExpLipschitzBudget r * ‖YA - YB‖ :=
    norm_exp_sub_exp_le_cmp102ExpLipschitzBudget hr hYA hYB
  unfold physicalMatrixExp
  exact hexp.trans (mul_le_mul_of_nonneg_left hdiff
    (cmp102ExpLipschitzBudget_nonneg r hr))

end

end YangMills.RG
