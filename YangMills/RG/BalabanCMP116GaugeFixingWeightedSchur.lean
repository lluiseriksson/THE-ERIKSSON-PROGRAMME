import YangMills.RG.BalabanCMP116GaugeFixingMassDefect
import YangMills.RG.PhysicalCoerciveCombesThomas
import YangMills.RG.PhysicalBondDistance

/-!
# Weighted Schur bounds for the background gauge-fixing defect

The gauge-fixing mass defect has exact physical-bond range two and block
kernel rate `4δ` under pointwise smallness of the adjoint action.  This module
converts those two physical facts into volume-independent weighted operator
bounds.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- Explicit block-kernel rate of the gauge-fixing mass defect. -/
def cmp116GaugeFixingMassDefectRate (δ : ℝ) : ℝ := 4 * δ

/-- Explicit physical-bond ball budget at range two. -/
def cmp116GaugeFixingRangeTwoBallBudget (d : ℕ) : ℕ :=
  (2 * (2 + 1)) ^ d * d

theorem cmp116GaugeFixingMassDefectRate_nonneg
    {δ : ℝ} (hδ : 0 ≤ δ) :
    0 ≤ cmp116GaugeFixingMassDefectRate δ := by
  unfold cmp116GaugeFixingMassDefectRate
  positivity

/-- Unweighted operator-norm bound for the gauge-fixing mass defect. -/
theorem norm_gaugeFixingMassDefectCLM_le
    (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hsmall : PhysicalAdjointSmallBackground ρ U δ) :
    ‖gaugeFixingMassDefectCLM ρ U‖ ≤
      cmp116GaugeFixingMassDefectRate δ *
        (cmp116GaugeFixingRangeTwoBallBudget d : ℝ) := by
  apply physicalOpNorm_le_of_kernelBound_finiteRange
    physicalBondDist physicalBondDist_comm
  · exact cmp116GaugeFixingMassDefectRate_nonneg hδ
  · intro x
    exact physicalBondDist_ball_card_le x 2
  · exact gaugeFixingMassDefectCLM_finiteRange ρ U
  · simpa [cmp116GaugeFixingMassDefectRate] using
      gaugeFixingMassDefectCLM_kernelBound ρ U hδ hsmall

/-- Weighted entrywise bound for the conjugated gauge-fixing mass defect. -/
theorem gaugeFixingMassDefect_tilt_kernelBound
    (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hsmall : PhysicalAdjointSmallBackground ρ U δ)
    (μ : ℝ) (hμ : 0 ≤ μ) (root : PhysicalBond d N) :
    PhysicalCovarianceKernelBound
      (physicalTiltConjCLM (Nc := Nc) physicalBondDist μ root
        (gaugeFixingMassDefectCLM ρ U))
      (fun _target _source =>
        cmp116GaugeFixingMassDefectRate δ *
          Real.exp (μ * (2 : ℝ))) := by
  exact physicalTiltConjCLM_kernelBound
    physicalBondDist physicalBondDist_comm physicalBondDist_triangle
    hμ root (cmp116GaugeFixingMassDefectRate_nonneg hδ)
    (gaugeFixingMassDefectCLM_finiteRange ρ U)
    (by
      simpa [cmp116GaugeFixingMassDefectRate] using
        gaugeFixingMassDefectCLM_kernelBound ρ U hδ hsmall)

/-- Weighted Schur bound for the conjugated gauge-fixing mass defect. -/
theorem norm_gaugeFixingMassDefect_tilt_le
    (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hsmall : PhysicalAdjointSmallBackground ρ U δ)
    (μ : ℝ) (hμ : 0 ≤ μ) (root : PhysicalBond d N) :
    ‖physicalTiltConjCLM (Nc := Nc) physicalBondDist μ root
        (gaugeFixingMassDefectCLM ρ U)‖ ≤
      cmp116GaugeFixingMassDefectRate δ *
        Real.exp (μ * (2 : ℝ)) *
        (cmp116GaugeFixingRangeTwoBallBudget d : ℝ) := by
  apply physicalOpNorm_le_of_kernelBound_finiteRange
    physicalBondDist physicalBondDist_comm
  · have hrate := cmp116GaugeFixingMassDefectRate_nonneg hδ
    positivity
  · intro x
    exact physicalBondDist_ball_card_le x 2
  · exact physicalTiltConjCLM_finiteRange physicalBondDist μ root
      (gaugeFixingMassDefectCLM_finiteRange ρ U)
  · exact gaugeFixingMassDefect_tilt_kernelBound
      ρ U hδ hsmall μ hμ root

/-- Weighted perturbation cost for the gauge-fixing mass defect. -/
theorem norm_gaugeFixingMassDefect_tilt_sub_le
    (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hsmall : PhysicalAdjointSmallBackground ρ U δ)
    (μ : ℝ) (hμ : 0 ≤ μ) (root : PhysicalBond d N) :
    ‖physicalTiltConjCLM (Nc := Nc) physicalBondDist μ root
          (gaugeFixingMassDefectCLM ρ U) -
        gaugeFixingMassDefectCLM ρ U‖ ≤
      cmp116GaugeFixingMassDefectRate δ *
        (Real.exp (μ * (2 : ℝ)) - 1) *
        (cmp116GaugeFixingRangeTwoBallBudget d : ℝ) := by
  exact norm_physicalTiltConj_sub_le
    physicalBondDist physicalBondDist_comm physicalBondDist_triangle
    hμ root (cmp116GaugeFixingMassDefectRate_nonneg hδ)
    (fun x => physicalBondDist_ball_card_le x 2)
    (gaugeFixingMassDefectCLM_finiteRange ρ U)
    (by
      simpa [cmp116GaugeFixingMassDefectRate] using
        gaugeFixingMassDefectCLM_kernelBound ρ U hδ hsmall)

end

end YangMills.RG
