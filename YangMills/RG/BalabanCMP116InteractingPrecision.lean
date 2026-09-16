import YangMills.RG.BalabanCMP116GaugeFixingWeightedSchur
import YangMills.RG.BalabanCMP116WilsonHessianWeightedSchur
import YangMills.RG.BalabanCMP116WilsonHessianOperator
import YangMills.RG.GaugeFixedPrecision

/-!
# Complete small-background precision: Wilson plus gauge fixing

This module assembles the two background-dependent pieces that must be
controlled before coercivity can be claimed:

* the literal Wilson Hessian;
* the covariant gauge-fixing mass `Q_U†Q_U`.

The block-constraint mass is unchanged.  The complete defect relative to the
flat precision is exactly the sum of the Wilson defect and the gauge-fixing
mass defect.  Their volume-uniform norm budgets then give coercivity survival.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

set_option synthInstance.maxHeartbeats 100000

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- Literal Wilson Hessian plus background covariant gauge-fixing mass. -/
noncomputable def interactingWilsonGaugeHodgeCLM
    (U : PhysicalGaugeBackground d N Nc) :
    PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc :=
  physicalWilsonHessianCLM U +
    gaugeFixingMassCLM (matrixSUNAdjointModel Nc) U

/-- Complete background defect relative to the flat Wilson-plus-gauge
operator. -/
noncomputable def interactingWilsonGaugeDefectCLM
    (U : PhysicalGaugeBackground d N Nc) :
    PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc :=
  physicalWilsonHessianDefectCLM U +
    gaugeFixingMassDefectCLM (matrixSUNAdjointModel Nc) U

/-- Exact decomposition into flat precision plus the two physical defects. -/
theorem interactingWilsonGaugeHodgeCLM_eq_flat_add_defect
    (U : PhysicalGaugeBackground d N Nc) :
    interactingWilsonGaugeHodgeCLM U =
      flatGaugeHodgeK0CLM d N Nc (matrixSUNAdjointModel Nc) +
        interactingWilsonGaugeDefectCLM U := by
  rw [←
    physicalWilsonHessianCLM_trivial_add_gaugeFixingMass_eq_flatGaugeHodge]
  apply ContinuousLinearMap.ext
  intro A
  simp only [interactingWilsonGaugeHodgeCLM,
    interactingWilsonGaugeDefectCLM,
    physicalWilsonHessianDefectCLM_apply,
    gaugeFixingMassDefectCLM_apply,
    ContinuousLinearMap.add_apply]
  abel

/-- Base precision at a small interacting background.  The block map is kept
generic because its mass is independent of the fine background in this
campaign. -/
noncomputable def interactingWilsonGaugeBasePrecisionCLM
    {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (U : PhysicalGaugeBackground d N Nc)
    (Q : PhysicalGaugeOneCochain d N Nc →L[ℝ] F)
    (a : ℝ) :
    PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc :=
  gaugeFixedBasePrecisionCLM (interactingWilsonGaugeHodgeCLM U) Q a

/-- The block mass cancels exactly in the interacting-minus-flat
decomposition. -/
theorem interactingWilsonGaugeBasePrecisionCLM_eq_flat_add_defect
    {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (U : PhysicalGaugeBackground d N Nc)
    (Q : PhysicalGaugeOneCochain d N Nc →L[ℝ] F)
    (a : ℝ) :
    interactingWilsonGaugeBasePrecisionCLM U Q a =
      gaugeFixedBasePrecisionCLM
          (flatGaugeHodgeK0CLM d N Nc (matrixSUNAdjointModel Nc)) Q a +
        interactingWilsonGaugeDefectCLM U := by
  rw [interactingWilsonGaugeBasePrecisionCLM,
    interactingWilsonGaugeHodgeCLM_eq_flat_add_defect]
  apply ContinuousLinearMap.ext
  intro A
  simp only [gaugeFixedBasePrecisionCLM,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  abel

/-- Explicit volume-uniform norm budget for the complete background defect. -/
def cmp116InteractingWilsonGaugeDefectBudget
    (d Nc : ℕ) (ε δ : ℝ) : ℝ :=
  cmp116WilsonHessianDefectRate d Nc ε +
    cmp116GaugeFixingMassDefectRate δ *
      (cmp116GaugeFixingRangeTwoBallBudget d : ℝ)

theorem norm_interactingWilsonGaugeDefectCLM_le
    (U : PhysicalGaugeBackground d N Nc)
    {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hWilson : PhysicalWilsonSmallBackground U ε)
    (hAdjoint :
      PhysicalAdjointSmallBackground (matrixSUNAdjointModel Nc) U δ) :
    ‖interactingWilsonGaugeDefectCLM U‖ ≤
      cmp116InteractingWilsonGaugeDefectBudget d Nc ε δ := by
  calc
    ‖interactingWilsonGaugeDefectCLM U‖ ≤
        ‖physicalWilsonHessianDefectCLM U‖ +
          ‖gaugeFixingMassDefectCLM (matrixSUNAdjointModel Nc) U‖ := by
      change
        ‖physicalWilsonHessianDefectCLM U +
            gaugeFixingMassDefectCLM (matrixSUNAdjointModel Nc) U‖ ≤ _
      exact norm_add_le
        (physicalWilsonHessianDefectCLM U)
        (gaugeFixingMassDefectCLM (matrixSUNAdjointModel Nc) U)
    _ ≤ cmp116WilsonHessianDefectRate d Nc ε +
        cmp116GaugeFixingMassDefectRate δ *
          (cmp116GaugeFixingRangeTwoBallBudget d : ℝ) :=
      add_le_add
        (by
          change
            ‖physicalWilsonHessianDefectCLM U‖ ≤
              ((256 * Nc * d : ℕ) : ℝ) * ε
          exact norm_physicalWilsonHessianDefectCLM_le U ε hε hWilson)
        (norm_gaugeFixingMassDefectCLM_le
          (matrixSUNAdjointModel Nc) U hδ hAdjoint)
    _ = cmp116InteractingWilsonGaugeDefectBudget d Nc ε δ := rfl

/-- Coercivity of the flat base precision survives at the interacting
background with the explicit complete-defect budget. -/
theorem isCoerciveCLM_interactingWilsonGaugeBasePrecision
    {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (U : PhysicalGaugeBackground d N Nc)
    (Q : PhysicalGaugeOneCochain d N Nc →L[ℝ] F)
    (a c : ℝ)
    {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hWilson : PhysicalWilsonSmallBackground U ε)
    (hAdjoint :
      PhysicalAdjointSmallBackground (matrixSUNAdjointModel Nc) U δ)
    (hflat :
      IsCoerciveCLM
        (gaugeFixedBasePrecisionCLM
          (flatGaugeHodgeK0CLM d N Nc (matrixSUNAdjointModel Nc)) Q a) c) :
    IsCoerciveCLM
      (interactingWilsonGaugeBasePrecisionCLM U Q a)
      (c - cmp116InteractingWilsonGaugeDefectBudget d Nc ε δ) := by
  rw [interactingWilsonGaugeBasePrecisionCLM_eq_flat_add_defect]
  exact isCoercive_add_of_opNorm_le _ _ hflat
    (norm_interactingWilsonGaugeDefectCLM_le
      U hε hδ hWilson hAdjoint)

end

end YangMills.RG
