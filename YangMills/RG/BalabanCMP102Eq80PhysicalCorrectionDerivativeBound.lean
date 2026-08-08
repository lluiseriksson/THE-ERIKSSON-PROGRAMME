/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalCorrectionLipschitz
import YangMills.RG.BalabanCMP102Eq80PhysicalCorrectionRegularity

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

/-- **Ambient first-jet producer.**  The source-generated sup-norm
first-derivative estimate transports back through the inverse physical
coordinate equivalence.  This is the correctly typed first jet of the
stored rectangular correction `Fine → Coarse`; the only additional cost is
the explicit inverse-equivalence norm. -/
theorem
    norm_iteratedFDeriv_one_cmp102Eq80PhysicalBackgroundCorrection_le_sourceBudget
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
    (hρ : ∀ A, 0 < ρ A)
    (hcontract : ∀ A, ((S A).toBallData).contractionRate < 1)
    (A : FinePhysicalOneCochain d L N' Nc) :
    ‖iteratedFDeriv ℝ 1
        (cmp102Eq80PhysicalBackgroundCorrection
          U ha hP hε hsmall hbudget ρ radius
            (fun _ => r) (fun _ => s) S hcontract)
        A‖ ≤
      ‖(physicalGaugeOneCochainSupEquiv
          (d := d) (N := N') (Nc := Nc)).symm.toContinuousLinearMap‖ *
        ((cmp102PhysicalCorrectionContractionRate Nc d L r s /
            (1 - ((S 0).toBallData).contractionRate)) *
          ‖(physicalGaugeOneCochainSupEquiv :
            FinePhysicalOneCochain d L N' Nc ≃L[ℝ]
              PhysicalGaugeOneCochainSup d (L * N') Nc
            ).toContinuousLinearMap‖) := by
  let g := fun X : FinePhysicalOneCochain d L N' Nc =>
    physicalGaugeOneCochainSupEquiv
      (cmp102Eq80PhysicalBackgroundCorrection
        U ha hP hε hsmall hbudget ρ radius
          (fun _ => r) (fun _ => s) S hcontract X)
  let inv :=
    (physicalGaugeOneCochainSupEquiv
      (d := d) (N := N') (Nc := Nc)).symm.toContinuousLinearMap
  have hg : ContDiffAt ℝ 1 g A := by
    exact
      (contDiff_cmp102Eq80PhysicalBackgroundCorrection_sup
        U ha hP hε hsmall hbudget ρ radius r s S hρ hcontract).contDiffAt.of_le
          (by norm_num)
  have hcomp :
      ‖iteratedFDeriv ℝ 1 (inv ∘ g) A‖ ≤
        ‖inv‖ * ‖iteratedFDeriv ℝ 1 g A‖ :=
    inv.norm_iteratedFDeriv_comp_left hg le_rfl
  have hsup :=
    norm_iteratedFDeriv_one_cmp102Eq80PhysicalBackgroundCorrection_sup_le
      U ha hP hε hsmall hbudget ρ radius r s S hcontract A
  have hfun :
      cmp102Eq80PhysicalBackgroundCorrection
          U ha hP hε hsmall hbudget ρ radius
            (fun _ => r) (fun _ => s) S hcontract =
        inv ∘ g := by
    funext X
    simp [inv, g]
  rw [hfun]
  exact hcomp.trans
    (mul_le_mul_of_nonneg_left hsup (norm_nonneg inv))

end

end YangMills.RG
