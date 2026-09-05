/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalCorrectionLinearBound

/-!
# Ambient-norm linear growth of the physical CMP102 correction

The fixed-point estimate is naturally volume-uniform in the physical
maximum norm.  This module transports it back to the stored finite `L²`
cochain norms.  The resulting constant may depend on the finite-volume norm
equivalences, which is harmless for the local Fréchet calculation, while the
underlying source estimate remains the volume-uniform theorem.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d L N' Nc : ℕ}
variable [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
  [NeZero (L * N')]

/-- The explicit finite-dimensional norm-transport constant multiplying the
source field in the physical fixed-point estimate. -/
noncomputable def cmp102Eq80PhysicalBackgroundCorrectionLinearGrowthConstant
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (ρ radius r s : FinePhysicalOneCochain d L N' Nc → ℝ)
    (S : ∀ A, CMP102PhysicalBackgroundCorrectionScalarData
      U ha hP hε hsmall hbudget A (ρ A) (radius A) (r A) (s A))
    (A : FinePhysicalOneCochain d L N' Nc) : ℝ :=
  ‖(physicalGaugeOneCochainSupEquiv
      (d := d) (N := N') (Nc := Nc)).symm.toContinuousLinearMap‖ *
    (cmp102PhysicalCorrectionContractionRate Nc d L (r A) (s A) /
      (1 - ((S A).toBallData).contractionRate)) *
    ‖(physicalGaugeOneCochainSupEquiv
      (d := d) (N := L * N') (Nc := Nc)).toContinuousLinearMap‖

set_option maxHeartbeats 10000000 in
/-- The physical equation-(80) correction has at most linear growth in the
ambient finite `L²` norm.  No differentiability of the selected fixed point
is assumed. -/
theorem norm_cmp102Eq80PhysicalBackgroundCorrection_le
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (ρ radius r s : FinePhysicalOneCochain d L N' Nc → ℝ)
    (S : ∀ A, CMP102PhysicalBackgroundCorrectionScalarData
      U ha hP hε hsmall hbudget A (ρ A) (radius A) (r A) (s A))
    (hcontract : ∀ A, ((S A).toBallData).contractionRate < 1)
    (A : FinePhysicalOneCochain d L N' Nc) :
    ‖cmp102Eq80PhysicalBackgroundCorrection
        U ha hP hε hsmall hbudget ρ radius r s S hcontract A‖ ≤
      cmp102Eq80PhysicalBackgroundCorrectionLinearGrowthConstant
        U ha hP hε hsmall hbudget ρ radius r s S A * ‖A‖ := by
  let D :=
    cmp102Eq80PhysicalBackgroundCorrection
      U ha hP hε hsmall hbudget ρ radius r s S hcontract A
  let C :=
    cmp102PhysicalCorrectionContractionRate Nc d L (r A) (s A) /
      (1 - ((S A).toBallData).contractionRate)
  let coarseSup :=
    physicalGaugeOneCochainSupEquiv
      (d := d) (N := N') (Nc := Nc)
  let fineSup :=
    physicalGaugeOneCochainSupEquiv
      (d := d) (N := L * N') (Nc := Nc)
  have hsup :
      cmp102PhysicalCorrectionSupNorm D ≤
        C * cmp98SourceFieldSupNorm A := by
    simpa [D, C] using
      cmp102Eq80PhysicalBackgroundCorrection_supNorm_le
        U ha hP hε hsmall hbudget ρ radius r s S hcontract A
  have hcoarse :
      ‖D‖ ≤ ‖coarseSup.symm.toContinuousLinearMap‖ *
          cmp102PhysicalCorrectionSupNorm D := by
    calc
      ‖D‖ = ‖coarseSup.symm (coarseSup D)‖ := by
        rw [ContinuousLinearEquiv.symm_apply_apply]
      _ ≤ ‖coarseSup.symm.toContinuousLinearMap‖ * ‖coarseSup D‖ :=
        coarseSup.symm.toContinuousLinearMap.le_opNorm (coarseSup D)
      _ = ‖coarseSup.symm.toContinuousLinearMap‖ *
          cmp102PhysicalCorrectionSupNorm D := by
        rw [norm_physicalGaugeOneCochainSupEquiv_eq_correctionSupNorm]
  have hfine :
      cmp98SourceFieldSupNorm A ≤
        ‖fineSup.toContinuousLinearMap‖ * ‖A‖ := by
    rw [← norm_physicalGaugeOneCochainSupEquiv_eq_sourceSupNorm]
    exact fineSup.toContinuousLinearMap.le_opNorm A
  have hC : 0 ≤ C := by
    have hnum :
        0 ≤ cmp102PhysicalCorrectionContractionRate
          Nc d L (r A) (s A) :=
      cmp102PhysicalCorrectionContractionRate_nonneg
        (r A) (s A) (S A).r_nonneg (S A).s_nonneg
    have hdenom :
        0 < 1 - ((S A).toBallData).contractionRate :=
      sub_pos.mpr (hcontract A)
    exact div_nonneg hnum hdenom.le
  calc
    ‖D‖ ≤ ‖coarseSup.symm.toContinuousLinearMap‖ *
        cmp102PhysicalCorrectionSupNorm D := hcoarse
    _ ≤ ‖coarseSup.symm.toContinuousLinearMap‖ *
        (C * cmp98SourceFieldSupNorm A) :=
      mul_le_mul_of_nonneg_left hsup (norm_nonneg _)
    _ ≤ ‖coarseSup.symm.toContinuousLinearMap‖ *
        (C * (‖fineSup.toContinuousLinearMap‖ * ‖A‖)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hfine hC) (norm_nonneg _)
    _ = cmp102Eq80PhysicalBackgroundCorrectionLinearGrowthConstant
          U ha hP hε hsmall hbudget ρ radius r s S A * ‖A‖ := by
      simp only
        [cmp102Eq80PhysicalBackgroundCorrectionLinearGrowthConstant,
          C, coarseSup, fineSup]
      ring

end

end YangMills.RG
