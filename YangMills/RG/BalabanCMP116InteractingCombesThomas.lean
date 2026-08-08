import YangMills.RG.BalabanCMP116AdjointSmallBridge
import YangMills.RG.PhysicalShellLocalityQ
import YangMills.RG.PhysicalCoerciveCombesThomasInverse

/-!
# Interacting CMP116 precision: concrete Combes--Thomas endpoint

The complete Wilson-plus-gauge precision is now controlled by the single
fundamental-link smallness condition.  This module combines that result with
the proved locality of the physical block constraint and the generic
Combes--Thomas ladder.

For a fixed finite shell and a supplied flat Hodge--Poincare certificate it
constructs the exact interacting covariance and proves an exponentially
decaying kernel bound with a positive rate whenever the explicit complete
defect budget leaves positive coercivity.

This does not construct the CMP116 random-walk decomposition or identify
`R₁`, `R₂`, and `R₃`.  It gives the exact localized inverse of the complete
physical precision that such a decomposition must refine.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

variable {d L N' Nc : ℕ}
  [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc] [NeZero (L * N')]

/-- The physical interacting base precision with the actual block constraint
on the fine `(L * N')` shell. -/
noncomputable def interactingPhysicalBasePrecisionCLM
    (U : PhysicalGaugeBackground d (L * N') Nc) (a : ℝ) :
    FinePhysicalOneCochain d L N' Nc →L[ℝ]
      FinePhysicalOneCochain d L N' Nc :=
  interactingWilsonGaugeBasePrecisionCLM U
    (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N') a

/-- Entrywise kernel budget for the full interacting physical precision. -/
def cmp116InteractingPhysicalKernelBudget
    (d L Nc : ℕ) (a ε : ℝ) : ℝ :=
  ((((4 * d : ℕ) : ℝ) ^ 2 + (2 : ℝ) ^ 2) +
      |a| * (L : ℝ) ^ 2) +
    ((((256 * Nc * d : ℕ) : ℝ) * ε) + 8 * ε)

theorem cmp116InteractingPhysicalKernelBudget_nonneg
    (a ε : ℝ) (hε : 0 ≤ ε) :
    0 ≤ cmp116InteractingPhysicalKernelBudget d L Nc a ε := by
  dsimp [cmp116InteractingPhysicalKernelBudget]
  positivity

/-- The complete background defect has range two. -/
theorem interactingWilsonGaugeDefectCLM_finiteRange
    (U : PhysicalGaugeBackground d (L * N') Nc) :
    PhysicalCovarianceFiniteRange
      (interactingWilsonGaugeDefectCLM U) physicalBondDist 2 := by
  unfold interactingWilsonGaugeDefectCLM
  exact physicalCovarianceFiniteRange_add physicalBondDist
    (physicalWilsonHessianDefectCLM_finiteRange U)
    (gaugeFixingMassDefectCLM_finiteRange (matrixSUNAdjointModel Nc) U)

/-- The full interacting physical base precision has the same common range
`3L` as the flat block precision. -/
theorem interactingPhysicalBasePrecisionCLM_finiteRange
    (U : PhysicalGaugeBackground d (L * N') Nc) (a : ℝ) :
    PhysicalCovarianceFiniteRange
      (interactingPhysicalBasePrecisionCLM U a)
      physicalBondDist (3 * L) := by
  rw [interactingPhysicalBasePrecisionCLM,
    interactingWilsonGaugeBasePrecisionCLM_eq_flat_add_defect]
  apply physicalCovarianceFiniteRange_add physicalBondDist
  · exact flatBasePrecision_finiteRange (matrixSUNAdjointModel Nc) a
  · apply physicalCovarianceFiniteRange_mono physicalBondDist
      (show 2 ≤ 3 * L by
        have := NeZero.one_le (n := L)
        omega)
    exact interactingWilsonGaugeDefectCLM_finiteRange U

/-- Entrywise kernel control of the complete interacting physical base
precision.  No ambient-volume factor occurs. -/
theorem interactingPhysicalBasePrecisionCLM_kernelBound
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (a : ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hsmall : PhysicalWilsonSmallBackground U ε) :
    PhysicalCovarianceKernelBound
      (interactingPhysicalBasePrecisionCLM U a)
      (fun _ _ => cmp116InteractingPhysicalKernelBudget d L Nc a ε) := by
  have hAdjoint :
      PhysicalAdjointSmallBackground
        (matrixSUNAdjointModel Nc) U (2 * ε) :=
    physicalAdjointSmallBackground_of_wilson U hsmall
  have hdef :
      PhysicalCovarianceKernelBound
        (interactingWilsonGaugeDefectCLM U)
        (fun _ _ =>
          (((256 * Nc * d : ℕ) : ℝ) * ε) + 8 * ε) := by
    unfold interactingWilsonGaugeDefectCLM
    have hsum := physicalCovarianceKernelBound_add
      (physicalWilsonHessianDefectCLM_kernelBound U ε hε hsmall)
      (gaugeFixingMassDefectCLM_kernelBound
        (matrixSUNAdjointModel Nc) U
        (mul_nonneg (by positivity) hε) hAdjoint)
    intro source target v
    simpa only [show 4 * (2 * ε) = 8 * ε by ring] using
      hsum source target v
  rw [interactingPhysicalBasePrecisionCLM,
    interactingWilsonGaugeBasePrecisionCLM_eq_flat_add_defect]
  have hsum := physicalCovarianceKernelBound_add
    (flatBasePrecision_kernelBound (matrixSUNAdjointModel Nc) a) hdef
  intro source target v
  simpa [cmp116InteractingPhysicalKernelBudget] using
    hsum source target v

/-- Coercivity of the complete interacting physical precision from the single
Wilson small-background hypothesis. -/
theorem isCoerciveCLM_interactingPhysicalBasePrecision
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP :
      FlatGaugeHodgePoincare d L N' Nc (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε)
    (hsmall : PhysicalWilsonSmallBackground U ε) :
    IsCoerciveCLM
      (interactingPhysicalBasePrecisionCLM U a)
      (min 1 a / CP -
        cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε) := by
  have hflat :
      IsCoerciveCLM
        (gaugeFixedBasePrecisionCLM
          (flatGaugeHodgeK0CLM d (L * N') Nc (matrixSUNAdjointModel Nc))
          (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N') a)
        (min 1 a / CP) :=
    isCoerciveCLM_gaugeFixedBasePrecision_of_blockPoincare
      _ _ ha.le hP.1
      (fun A =>
        flatGaugeHodgeK0_nonnegative_right
          (d := d) (N := L * N') (Nc := Nc)
          (matrixSUNAdjointModel Nc) A)
      hP.2
  exact isCoerciveCLM_interactingWilsonGaugeBasePrecision_of_wilson
    U (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N')
    a (min 1 a / CP) hε hsmall hflat

/-- Exact interacting covariance produced from the surviving coercivity. -/
noncomputable def interactingPhysicalCovarianceCLM
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP :
      FlatGaugeHodgePoincare d L N' Nc (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε)
    (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget :
      cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
        min 1 a / CP) :
    FinePhysicalOneCochain d L N' Nc →L[ℝ]
      FinePhysicalOneCochain d L N' Nc :=
  covarianceOfIsCoerciveCLM
    (interactingPhysicalBasePrecisionCLM U a)
    (sub_pos.mpr hbudget)
    (isCoerciveCLM_interactingPhysicalBasePrecision
      U ha hP hε hsmall)

/-- The interacting covariance is the exact right inverse of the complete
physical precision. -/
theorem interactingPhysicalBasePrecision_comp_covariance
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP :
      FlatGaugeHodgePoincare d L N' Nc (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε)
    (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget :
      cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
        min 1 a / CP) :
    (interactingPhysicalBasePrecisionCLM U a).comp
        (interactingPhysicalCovarianceCLM
          U ha hP hε hsmall hbudget) =
      ContinuousLinearMap.id ℝ
        (FinePhysicalOneCochain d L N' Nc) := by
  exact precision_comp_covarianceOfIsCoerciveCLM
    (interactingPhysicalBasePrecisionCLM U a)
    (sub_pos.mpr hbudget)
    (isCoerciveCLM_interactingPhysicalBasePrecision
      U ha hP hε hsmall)

/-- Concrete Combes--Thomas kernel estimate for the complete interacting
physical covariance. -/
theorem interactingPhysicalCovariance_CT
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε θ : ℝ} (ha : 0 < a)
    (hP :
      FlatGaugeHodgePoincare d L N' Nc (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε)
    (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget :
      cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
        min 1 a / CP)
    (hθ : 0 < θ)
    (htilt :
      cmp116InteractingPhysicalKernelBudget d L Nc a ε *
          (Real.exp (θ * ((3 * L : ℕ) : ℝ)) - 1) *
          (((2 * (3 * L + 1)) ^ d * d : ℕ) : ℝ)
        ≤
          (min 1 a / CP -
            cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε) / 2) :
    PhysicalCovarianceExponentialKernelBound
      (interactingPhysicalCovarianceCLM
        U ha hP hε hsmall hbudget)
      physicalBondDist
      (2 /
        (min 1 a / CP -
          cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε))
      θ := by
  exact physicalCovariance_exponentialKernelBound_of_coercive
    physicalBondDist physicalBondDist_comm physicalBondDist_triangle
    physicalBondDist_self hθ
    (cmp116InteractingPhysicalKernelBudget_nonneg a ε hε)
    (sub_pos.mpr hbudget)
    (fun x => physicalBondDist_ball_card_le x (3 * L))
    (interactingPhysicalBasePrecisionCLM_finiteRange U a)
    (interactingPhysicalBasePrecisionCLM_kernelBound U a hε hsmall)
    (isCoerciveCLM_interactingPhysicalBasePrecision U ha hP hε hsmall)
    (interactingPhysicalBasePrecision_comp_covariance
      U ha hP hε hsmall hbudget)
    htilt

/-- A positive exponential-decay rate exists whenever the complete defect
budget leaves positive coercivity. -/
theorem exists_interactingPhysicalCovariance_CT
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP :
      FlatGaugeHodgePoincare d L N' Nc (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε)
    (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget :
      cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
        min 1 a / CP) :
    ∃ θ : ℝ, 0 < θ ∧
      PhysicalCovarianceExponentialKernelBound
        (interactingPhysicalCovarianceCLM
          U ha hP hε hsmall hbudget)
        physicalBondDist
        (2 /
          (min 1 a / CP -
            cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε))
        θ := by
  obtain ⟨θ, hθ, htilt⟩ :=
    exists_pos_tiltBudget
      (3 * L) ((2 * (3 * L + 1)) ^ d * d)
      (M := cmp116InteractingPhysicalKernelBudget d L Nc a ε)
      (cmp116InteractingPhysicalKernelBudget_nonneg a ε hε)
      (sub_pos.mpr hbudget)
  exact ⟨θ, hθ,
    interactingPhysicalCovariance_CT
      U ha hP hε hsmall hbudget hθ htilt⟩

end

end YangMills.RG
