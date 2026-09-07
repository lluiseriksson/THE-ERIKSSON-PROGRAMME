/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalCorrection
import YangMills.RG.BalabanCMP102PhysicalCorrectionChartIndependence

/-!
# Independence of the CMP102 fixed point from scalar certificates

The scalar packages used by the Banach argument may vary with the fine
field.  They certify existence on a convenient ball, but they do not define
the physical correction.  This file proves that any two such packages with
the same physical parameters select the same solution.

This removes the certificate choice before any regularity argument for the
implicit correction.  It does not assume continuity or differentiability of
the selected packages.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d L N' Nc : ℕ}
variable [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
  [NeZero (L * N')]

/-- Pointwise certificate independence of the physical CMP102 background
correction.  The proof compares the two literal fixed-point equations after
removing their chart certificates. -/
theorem cmp102Eq80PhysicalBackgroundCorrection_independent
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (ρ radius r s : FinePhysicalOneCochain d L N' Nc → ℝ)
    (S₁ S₂ : ∀ A, CMP102PhysicalBackgroundCorrectionScalarData
      U ha hP hε hsmall hbudget A (ρ A) (radius A) (r A) (s A))
    (hcontract₁ : ∀ A, ((S₁ A).toBallData).contractionRate < 1)
    (hcontract₂ : ∀ A, ((S₂ A).toBallData).contractionRate < 1)
    (A : FinePhysicalOneCochain d L N' Nc) :
    cmp102Eq80PhysicalBackgroundCorrection
        U ha hP hε hsmall hbudget ρ radius r s S₁ hcontract₁ A =
      cmp102Eq80PhysicalBackgroundCorrection
        U ha hP hε hsmall hbudget ρ radius r s S₂ hcontract₂ A := by
  let B₁ := (S₁ A).toBallData
  let B₂ := (S₂ A).toBallData
  let D₁ : PhysicalGaugeOneCochainSup d N' Nc :=
    Classical.choose ((S₁ A).existsUnique_backgroundCorrection
      (hcontract₁ A))
  let D₂ : PhysicalGaugeOneCochainSup d N' Nc :=
    Classical.choose ((S₂ A).existsUnique_backgroundCorrection
      (hcontract₂ A))
  have hspec₁ :=
    Classical.choose_spec ((S₁ A).existsUnique_backgroundCorrection
      (hcontract₁ A))
  have hspec₂ :=
    Classical.choose_spec ((S₂ A).existsUnique_backgroundCorrection
      (hcontract₂ A))
  have hD₁ : ‖D₁‖ ≤ ρ A := hspec₁.1.1
  have hD₂ : ‖D₂‖ ≤ ρ A := hspec₂.1.1
  have heq₁ :
      physicalGaugeOneCochainSupEquiv
          (cmp102PhysicalNonlinearCorrectionOfBudget U
            (A - cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget
              (physicalGaugeOneCochainSupEquiv.symm D₁))
            (B₁.chartBudget D₁ hD₁)) = D₁ := by
    rw [← B₁.correctionMap_eq_of_mem D₁ hD₁]
    exact hspec₁.1.2
  have heq₁' :
      physicalGaugeOneCochainSupEquiv
          (cmp102PhysicalNonlinearCorrectionOfBudget U
            (A - cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget
              (physicalGaugeOneCochainSupEquiv.symm D₁))
            (B₂.chartBudget D₁ hD₁)) = D₁ := by
    rw [cmp102PhysicalNonlinearCorrectionOfBudget_independent
      U
      (A - cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget
        (physicalGaugeOneCochainSupEquiv.symm D₁))
      (B₂.chartBudget D₁ hD₁) (B₁.chartBudget D₁ hD₁)]
    exact heq₁
  have heq₂ :
      physicalGaugeOneCochainSupEquiv
          (cmp102PhysicalNonlinearCorrectionOfBudget U
            (A - cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget
              (physicalGaugeOneCochainSupEquiv.symm D₂))
            (B₂.chartBudget D₂ hD₂)) = D₂ := by
    rw [← B₂.correctionMap_eq_of_mem D₂ hD₂]
    exact hspec₂.1.2
  have hD :
      D₁ = D₂ :=
    B₂.backgroundCorrection_physicalEquation_unique
      (hcontract₂ A) D₁ D₂ hD₁ hD₂ heq₁' heq₂
  exact congrArg physicalGaugeOneCochainSupEquiv.symm hD

/-- Functional form of certificate independence. -/
theorem cmp102Eq80PhysicalBackgroundCorrection_fun_independent
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (ρ radius r s : FinePhysicalOneCochain d L N' Nc → ℝ)
    (S₁ S₂ : ∀ A, CMP102PhysicalBackgroundCorrectionScalarData
      U ha hP hε hsmall hbudget A (ρ A) (radius A) (r A) (s A))
    (hcontract₁ : ∀ A, ((S₁ A).toBallData).contractionRate < 1)
    (hcontract₂ : ∀ A, ((S₂ A).toBallData).contractionRate < 1) :
    cmp102Eq80PhysicalBackgroundCorrection
        U ha hP hε hsmall hbudget ρ radius r s S₁ hcontract₁ =
      cmp102Eq80PhysicalBackgroundCorrection
        U ha hP hε hsmall hbudget ρ radius r s S₂ hcontract₂ := by
  funext A
  exact cmp102Eq80PhysicalBackgroundCorrection_independent
    U ha hP hε hsmall hbudget ρ radius r s
    S₁ S₂ hcontract₁ hcontract₂ A

end

end YangMills.RG
