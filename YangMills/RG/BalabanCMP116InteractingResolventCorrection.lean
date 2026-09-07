/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116InteractingCombesThomas
import YangMills.RG.PhysicalResolventCorrection

/-!
# Exponentially localized interacting covariance correction

For two physical Wilson backgrounds `U₀` and `U₁`, this module compares the
exact complete covariances of the Wilson Hessian, covariant gauge-fixing mass,
and physical block constraint.  The second resolvent identity is combined with
the already proved weighted bounds for the complete background defect.

The result is an explicit exponentially decaying kernel estimate for

`C(U₁) - C(U₀)`,

with amplitude proportional to the two physical small-background budgets and
with no factor depending on the periodic volume.

Honest scope: this constructs a genuine physical covariance correction.  It
does not identify this operator difference with any particular CMP116
`R₁`, `R₂`, or `R₃`; the random-walk decomposition and the source-specific
assignment of those three kernels remain open.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

variable {d L N' Nc : ℕ}
  [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc] [NeZero (L * N')]

/-- Residual coercivity of the complete interacting precision. -/
def cmp116InteractingResidualCoercivity
    (d Nc : ℕ) (a CP ε : ℝ) : ℝ :=
  min 1 a / CP -
    cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε

/-- Weighted norm budget for the complete interacting defect relative to the
trivial background.  Both physical pieces have exact range two. -/
def cmp116InteractingTiltedDefectBudget
    (d Nc : ℕ) (ε θ : ℝ) : ℝ :=
  cmp116WilsonHessianDefectRate d Nc ε *
      Real.exp (θ * (2 : ℝ)) *
      (cmp116WilsonHessianRangeTwoBallBudget d : ℝ) +
    cmp116GaugeFixingMassDefectRate (2 * ε) *
      Real.exp (θ * (2 : ℝ)) *
      (cmp116GaugeFixingRangeTwoBallBudget d : ℝ)

theorem cmp116InteractingTiltedDefectBudget_nonneg
    {ε θ : ℝ} (hε : 0 ≤ ε) :
    0 ≤ cmp116InteractingTiltedDefectBudget d Nc ε θ := by
  unfold cmp116InteractingTiltedDefectBudget
  have hWilson :=
    cmp116WilsonHessianDefectRate_nonneg (d := d) (Nc := Nc) ε hε
  have hGauge :=
    cmp116GaugeFixingMassDefectRate_nonneg
      (δ := 2 * ε) (mul_nonneg (by positivity) hε)
  positivity

/-- The complete interacting defect has the explicit weighted norm budget. -/
theorem norm_interactingWilsonGaugeDefect_tilt_le
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {ε θ : ℝ} (hε : 0 ≤ ε)
    (hsmall : PhysicalWilsonSmallBackground U ε)
    (hθ : 0 ≤ θ) (root : PhysicalBond d (L * N')) :
    ‖physicalTiltConjCLM (Nc := Nc) physicalBondDist θ root
        (interactingWilsonGaugeDefectCLM U)‖ ≤
      cmp116InteractingTiltedDefectBudget d Nc ε θ := by
  rw [interactingWilsonGaugeDefectCLM, physicalTiltConjCLM_add]
  calc
    ‖physicalTiltConjCLM (Nc := Nc) physicalBondDist θ root
          (physicalWilsonHessianDefectCLM U) +
        physicalTiltConjCLM (Nc := Nc) physicalBondDist θ root
          (gaugeFixingMassDefectCLM (matrixSUNAdjointModel Nc) U)‖
        ≤
          ‖physicalTiltConjCLM (Nc := Nc) physicalBondDist θ root
            (physicalWilsonHessianDefectCLM U)‖ +
          ‖physicalTiltConjCLM (Nc := Nc) physicalBondDist θ root
            (gaugeFixingMassDefectCLM (matrixSUNAdjointModel Nc) U)‖ :=
      norm_add_le _ _
    _ ≤
        cmp116WilsonHessianDefectRate d Nc ε *
            Real.exp (θ * (2 : ℝ)) *
            (cmp116WilsonHessianRangeTwoBallBudget d : ℝ) +
          cmp116GaugeFixingMassDefectRate (2 * ε) *
            Real.exp (θ * (2 : ℝ)) *
            (cmp116GaugeFixingRangeTwoBallBudget d : ℝ) :=
      add_le_add
        (norm_physicalWilsonHessianDefect_tilt_le
          U ε hε hsmall θ hθ root)
        (norm_gaugeFixingMassDefect_tilt_le
          (matrixSUNAdjointModel Nc) U
          (mul_nonneg (by positivity) hε)
          (physicalAdjointSmallBackground_of_wilson U hsmall)
          θ hθ root)
    _ = cmp116InteractingTiltedDefectBudget d Nc ε θ := rfl

/-- Exact cancellation of the common flat precision between two interacting
backgrounds. -/
theorem interactingPhysicalBasePrecisionCLM_sub_eq_defect_sub
    (U₀ U₁ : PhysicalGaugeBackground d (L * N') Nc)
    (a : ℝ) :
    interactingPhysicalBasePrecisionCLM U₀ a -
        interactingPhysicalBasePrecisionCLM U₁ a =
      interactingWilsonGaugeDefectCLM U₀ -
        interactingWilsonGaugeDefectCLM U₁ := by
  rw [interactingPhysicalBasePrecisionCLM,
    interactingPhysicalBasePrecisionCLM,
    interactingWilsonGaugeBasePrecisionCLM_eq_flat_add_defect,
    interactingWilsonGaugeBasePrecisionCLM_eq_flat_add_defect]
  abel

/-- Weighted norm bound for the precision difference of two physical small
backgrounds. -/
theorem norm_interactingPhysicalBasePrecision_sub_tilt_le
    (U₀ U₁ : PhysicalGaugeBackground d (L * N') Nc)
    (a : ℝ)
    {ε₀ ε₁ θ : ℝ}
    (hε₀ : 0 ≤ ε₀) (hε₁ : 0 ≤ ε₁)
    (hsmall₀ : PhysicalWilsonSmallBackground U₀ ε₀)
    (hsmall₁ : PhysicalWilsonSmallBackground U₁ ε₁)
    (hθ : 0 ≤ θ) (root : PhysicalBond d (L * N')) :
    ‖physicalTiltConjCLM (Nc := Nc) physicalBondDist θ root
        (interactingPhysicalBasePrecisionCLM U₀ a -
          interactingPhysicalBasePrecisionCLM U₁ a)‖ ≤
      cmp116InteractingTiltedDefectBudget d Nc ε₀ θ +
        cmp116InteractingTiltedDefectBudget d Nc ε₁ θ := by
  rw [interactingPhysicalBasePrecisionCLM_sub_eq_defect_sub,
    physicalTiltConjCLM_sub]
  exact (norm_sub_le _ _).trans
    (add_le_add
      (norm_interactingWilsonGaugeDefect_tilt_le
        U₀ hε₀ hsmall₀ hθ root)
      (norm_interactingWilsonGaugeDefect_tilt_le
        U₁ hε₁ hsmall₁ hθ root))

/-- The exact interacting covariance is also the left inverse of its complete
physical precision. -/
theorem interactingPhysicalCovariance_comp_basePrecision
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP :
      FlatGaugeHodgePoincare d L N' Nc (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε)
    (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget :
      cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
        min 1 a / CP) :
    (interactingPhysicalCovarianceCLM
        U ha hP hε hsmall hbudget).comp
      (interactingPhysicalBasePrecisionCLM U a) =
        ContinuousLinearMap.id ℝ
          (FinePhysicalOneCochain d L N' Nc) := by
  exact covarianceOfIsCoerciveCLM_comp_precision
    (interactingPhysicalBasePrecisionCLM U a)
    (sub_pos.mpr hbudget)
    (isCoerciveCLM_interactingPhysicalBasePrecision
      U ha hP hε hsmall)

/-- Complete physical covariance correction between two small backgrounds.
The constants are fixed-volume only through the supplied Poincare constant
`CP`; no ambient cardinality enters the correction amplitude. -/
theorem interactingPhysicalCovariance_sub_exponentialKernelBound
    (U₀ U₁ : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε₀ ε₁ θ : ℝ}
    (ha : 0 < a)
    (hP :
      FlatGaugeHodgePoincare d L N' Nc (matrixSUNAdjointModel Nc) CP)
    (hε₀ : 0 ≤ ε₀) (hε₁ : 0 ≤ ε₁)
    (hsmall₀ : PhysicalWilsonSmallBackground U₀ ε₀)
    (hsmall₁ : PhysicalWilsonSmallBackground U₁ ε₁)
    (hbudget₀ :
      cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε₀ <
        min 1 a / CP)
    (hbudget₁ :
      cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε₁ <
        min 1 a / CP)
    (hθ : 0 < θ)
    (htilt₀ :
      cmp116InteractingPhysicalKernelBudget d L Nc a ε₀ *
          (Real.exp (θ * ((3 * L : ℕ) : ℝ)) - 1) *
          (((2 * (3 * L + 1)) ^ d * d : ℕ) : ℝ)
        ≤ cmp116InteractingResidualCoercivity d Nc a CP ε₀ / 2)
    (htilt₁ :
      cmp116InteractingPhysicalKernelBudget d L Nc a ε₁ *
          (Real.exp (θ * ((3 * L : ℕ) : ℝ)) - 1) *
          (((2 * (3 * L + 1)) ^ d * d : ℕ) : ℝ)
        ≤ cmp116InteractingResidualCoercivity d Nc a CP ε₁ / 2) :
    PhysicalCovarianceExponentialKernelBound
      (interactingPhysicalCovarianceCLM
          U₁ ha hP hε₁ hsmall₁ hbudget₁ -
        interactingPhysicalCovarianceCLM
          U₀ ha hP hε₀ hsmall₀ hbudget₀)
      physicalBondDist
      ((2 / cmp116InteractingResidualCoercivity d Nc a CP ε₁) *
        (cmp116InteractingTiltedDefectBudget d Nc ε₀ θ +
          cmp116InteractingTiltedDefectBudget d Nc ε₁ θ) *
        (2 / cmp116InteractingResidualCoercivity d Nc a CP ε₀))
      θ := by
  let K₀ := interactingPhysicalBasePrecisionCLM U₀ a
  let K₁ := interactingPhysicalBasePrecisionCLM U₁ a
  let C₀ := interactingPhysicalCovarianceCLM
    U₀ ha hP hε₀ hsmall₀ hbudget₀
  let C₁ := interactingPhysicalCovarianceCLM
    U₁ ha hP hε₁ hsmall₁ hbudget₁
  have hc₀ :
      0 < cmp116InteractingResidualCoercivity d Nc a CP ε₀ := by
    exact sub_pos.mpr hbudget₀
  have hc₁ :
      0 < cmp116InteractingResidualCoercivity d Nc a CP ε₁ := by
    exact sub_pos.mpr hbudget₁
  apply physicalCovarianceExponentialKernelBound_sub_of_tilted_resolvent
    physicalBondDist physicalBondDist_comm physicalBondDist_self
    hθ hc₀ hc₁
    (add_nonneg
      (cmp116InteractingTiltedDefectBudget_nonneg hε₀)
      (cmp116InteractingTiltedDefectBudget_nonneg hε₁))
    K₀ K₁ C₀ C₁
  · exact interactingPhysicalCovariance_comp_basePrecision
      U₁ ha hP hε₁ hsmall₁ hbudget₁
  · exact interactingPhysicalBasePrecision_comp_covariance
      U₀ ha hP hε₀ hsmall₀ hbudget₀
  · exact interactingPhysicalBasePrecision_comp_covariance
      U₁ ha hP hε₁ hsmall₁ hbudget₁
  · intro root
    exact isCoerciveCLM_physicalTiltConj_half
      physicalBondDist physicalBondDist_comm physicalBondDist_triangle
      hθ.le root
      (cmp116InteractingPhysicalKernelBudget_nonneg a ε₀ hε₀)
      (fun x => physicalBondDist_ball_card_le x (3 * L))
      (interactingPhysicalBasePrecisionCLM_finiteRange U₀ a)
      (interactingPhysicalBasePrecisionCLM_kernelBound U₀ a hε₀ hsmall₀)
      (isCoerciveCLM_interactingPhysicalBasePrecision
        U₀ ha hP hε₀ hsmall₀)
      htilt₀
  · intro root
    exact isCoerciveCLM_physicalTiltConj_half
      physicalBondDist physicalBondDist_comm physicalBondDist_triangle
      hθ.le root
      (cmp116InteractingPhysicalKernelBudget_nonneg a ε₁ hε₁)
      (fun x => physicalBondDist_ball_card_le x (3 * L))
      (interactingPhysicalBasePrecisionCLM_finiteRange U₁ a)
      (interactingPhysicalBasePrecisionCLM_kernelBound U₁ a hε₁ hsmall₁)
      (isCoerciveCLM_interactingPhysicalBasePrecision
        U₁ ha hP hε₁ hsmall₁)
      htilt₁
  · intro root
    exact norm_interactingPhysicalBasePrecision_sub_tilt_le
      U₀ U₁ a hε₀ hε₁ hsmall₀ hsmall₁ hθ.le root

end

end YangMills.RG
