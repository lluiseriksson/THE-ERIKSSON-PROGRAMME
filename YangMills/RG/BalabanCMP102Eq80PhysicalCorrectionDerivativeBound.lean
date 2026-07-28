/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalCorrectionLipschitz

/-!
# Quantitative first derivative of the physical CMP102 correction

The selected correction is globally Lipschitz after transport to the
source sup-norm Banach space.  The converse mean-value inequality therefore
controls its actual Fréchet derivative at every fine field by the same
explicit physical constant.

This is the first quantitative source-jet producer for the selected
correction.  It does not claim bounds for derivatives of order at least two.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d L N' Nc : ℕ}
variable [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
  [NeZero (L * N')]

/-- The actual first Fréchet derivative of the selected physical correction,
in its source sup-norm realization, is bounded by the explicit fixed-point
Lipschitz constant. -/
theorem norm_fderiv_cmp102Eq80PhysicalBackgroundCorrection_sup_le
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (ρ radius : FinePhysicalOneCochain d L N' Nc → ℝ)
    (r s : ℝ)
    (S : ∀ A, CMP102PhysicalBackgroundCorrectionScalarData
      U ha hP hε hsmall hbudget A (ρ A) (radius A) r s)
    (hcontract : ∀ A, ((S A).toBallData).contractionRate < 1)
    (A : FinePhysicalOneCochain d L N' Nc) :
    ‖fderiv ℝ
        (fun X =>
          physicalGaugeOneCochainSupEquiv
            (cmp102Eq80PhysicalBackgroundCorrection
              U ha hP hε hsmall hbudget ρ radius
                (fun _ => r) (fun _ => s) S hcontract X))
        A‖ ≤
      (cmp102PhysicalCorrectionContractionRate Nc d L r s /
          (1 - ((S 0).toBallData).contractionRate)) *
        ‖(physicalGaugeOneCochainSupEquiv :
          FinePhysicalOneCochain d L N' Nc ≃L[ℝ]
            PhysicalGaugeOneCochainSup d (L * N') Nc
          ).toContinuousLinearMap‖ := by
  have h :=
    norm_fderiv_le_of_lipschitz ℝ
      (lipschitzWith_cmp102Eq80PhysicalBackgroundCorrection_sup
        U ha hP hε hsmall hbudget ρ radius r s S hcontract :
        LipschitzWith _
          (fun X =>
            physicalGaugeOneCochainSupEquiv
              (cmp102Eq80PhysicalBackgroundCorrection
                U ha hP hε hsmall hbudget ρ radius
                  (fun _ => r) (fun _ => s) S hcontract X)))
      (x₀ := A)
  simpa only [NNReal.coe_mk] using h

/-- Equivalent first iterated-derivative form, ready for source-jet
majorants. -/
theorem norm_iteratedFDeriv_one_cmp102Eq80PhysicalBackgroundCorrection_sup_le
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (ρ radius : FinePhysicalOneCochain d L N' Nc → ℝ)
    (r s : ℝ)
    (S : ∀ A, CMP102PhysicalBackgroundCorrectionScalarData
      U ha hP hε hsmall hbudget A (ρ A) (radius A) r s)
    (hcontract : ∀ A, ((S A).toBallData).contractionRate < 1)
    (A : FinePhysicalOneCochain d L N' Nc) :
    ‖iteratedFDeriv ℝ 1
        (fun X =>
          physicalGaugeOneCochainSupEquiv
            (cmp102Eq80PhysicalBackgroundCorrection
              U ha hP hε hsmall hbudget ρ radius
                (fun _ => r) (fun _ => s) S hcontract X))
        A‖ ≤
      (cmp102PhysicalCorrectionContractionRate Nc d L r s /
          (1 - ((S 0).toBallData).contractionRate)) *
        ‖(physicalGaugeOneCochainSupEquiv :
          FinePhysicalOneCochain d L N' Nc ≃L[ℝ]
            PhysicalGaugeOneCochainSup d (L * N') Nc
          ).toContinuousLinearMap‖ := by
  simpa only [norm_iteratedFDeriv_one] using
    norm_fderiv_cmp102Eq80PhysicalBackgroundCorrection_sup_le
      U ha hP hε hsmall hbudget ρ radius r s S hcontract A

end

end YangMills.RG
