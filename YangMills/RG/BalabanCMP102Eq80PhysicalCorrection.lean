/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalBackgroundCorrectionScalarFixedPoint
import YangMills.RG.BalabanCMP102PhysicalCorrectionZero
import YangMills.RG.BalabanCMP102Eq80PhysicalH

/-!
# The physical CMP102 correction inside equation (80)

Equation (80) previously accepted an arbitrary function `D(A')`.  This
module replaces it by the unique solution of the literal physical correction
equation `D = C(A' - H D)`, constructed pointwise from scalar source data.

The distinct source ingredients `D₃`, `V₀`, `Δπ`, and `J` remain explicit.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d L N' Nc : ℕ}
variable [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
  [NeZero (L * N')]

/-- The unique physical coarse correction associated to each fine field. -/
noncomputable def cmp102Eq80PhysicalBackgroundCorrection
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
    CoarsePhysicalOneCochain d N' Nc :=
  physicalGaugeOneCochainSupEquiv.symm
    (Classical.choose ((S A).existsUnique_backgroundCorrection
      (hcontract A)))

/-- The chosen correction lies in its certified source-sup ball. -/
theorem cmp102Eq80PhysicalBackgroundCorrection_mem_ball
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
    cmp102PhysicalCorrectionSupNorm
        (cmp102Eq80PhysicalBackgroundCorrection
          U ha hP hε hsmall hbudget ρ radius r s S hcontract A) ≤ ρ A := by
  rw [← norm_physicalGaugeOneCochainSupEquiv_eq_correctionSupNorm]
  simp only [cmp102Eq80PhysicalBackgroundCorrection]
  exact
    (Classical.choose_spec
      ((S A).existsUnique_backgroundCorrection (hcontract A))).1.1

/-- **Physical correction equation used by CMP102 (80).**  The selected
coarse field is exactly the nonlinear correction of the shifted fine field. -/
theorem cmp102Eq80PhysicalBackgroundCorrection_eq
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
    let Dsup :=
      Classical.choose ((S A).existsUnique_backgroundCorrection
        (hcontract A))
    cmp102PhysicalNonlinearCorrectionOfBudget U
        (A - cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget
          (cmp102Eq80PhysicalBackgroundCorrection
            U ha hP hε hsmall hbudget ρ radius r s S hcontract A))
        ((S A).toBallData.chartBudget Dsup
          (Classical.choose_spec
            ((S A).existsUnique_backgroundCorrection
              (hcontract A))).1.1) =
      cmp102Eq80PhysicalBackgroundCorrection
        U ha hP hε hsmall hbudget ρ radius r s S hcontract A := by
  dsimp only
  let Dsup :=
    Classical.choose ((S A).existsUnique_backgroundCorrection
      (hcontract A))
  have hspec :=
    Classical.choose_spec
      ((S A).existsUnique_backgroundCorrection (hcontract A))
  have hmap := hspec.1.2
  rw [(S A).toBallData.correctionMap_eq_of_mem Dsup hspec.1.1] at hmap
  have := congrArg physicalGaugeOneCochainSupEquiv.symm hmap
  simpa [Dsup, cmp102Eq80PhysicalBackgroundCorrection] using this

/-- The unique physical correction is normalized at the zero fine field. -/
@[simp] theorem cmp102Eq80PhysicalBackgroundCorrection_zero
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
    (hcontract : ∀ A, ((S A).toBallData).contractionRate < 1) :
    cmp102Eq80PhysicalBackgroundCorrection
      U ha hP hε hsmall hbudget ρ radius r s S hcontract 0 = 0 := by
  let Dsup :=
    Classical.choose ((S 0).existsUnique_backgroundCorrection
      (hcontract 0))
  have hspec :=
    Classical.choose_spec
      ((S 0).existsUnique_backgroundCorrection (hcontract 0))
  have hzero :
      ‖(0 : PhysicalGaugeOneCochainSup d N' Nc)‖ ≤ ρ 0 := by
    simpa using (S 0).rho_nonneg
  have hmapzero :
      cmp102PhysicalBackgroundCorrectionMap
          U ha hP hε hsmall hbudget 0 (ρ 0) (r 0) (s 0)
          (S 0).toBallData 0 = 0 := by
    rw [(S 0).toBallData.correctionMap_eq_of_mem 0 hzero]
    have hX :
        (0 : FinePhysicalOneCochain d L N' Nc) -
            cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget
              (physicalGaugeOneCochainSupEquiv.symm 0) = 0 := by
      rw [map_zero, map_zero, sub_zero]
    rw [cmp102PhysicalNonlinearCorrectionOfBudget_eq_zero_of_eq_zero
      U hX, map_zero]
  have hDsup : Dsup = 0 :=
    (hspec.2 0 ⟨hzero, hmapzero⟩).symm
  change physicalGaugeOneCochainSupEquiv.symm Dsup = 0
  rw [hDsup, map_zero]

/-- Equation (80) with `D(A')` fixed to the physical CMP102 correction. -/
noncomputable def cmp102Eq80CorrectedPhysicalGlobalPotential
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
    (D₃ : FinePhysicalOneCochain d L N' Nc →
      CoarsePhysicalOneCochain d N' Nc)
    (V₀ : FinePhysicalOneCochain d L N' Nc → ℝ)
    (Δπ : FinePhysicalOneCochain d L N' Nc →L[ℝ]
      FinePhysicalOneCochain d L N' Nc)
    (J A' : FinePhysicalOneCochain d L N' Nc) : ℝ :=
  cmp102Eq80PhysicalGlobalPotential U ha hP hε hsmall hbudget
    (cmp102Eq80PhysicalBackgroundCorrection
      U ha hP hε hsmall hbudget ρ radius r s S hcontract)
    D₃ V₀ Δπ J A'

/-- The corrected equation-(80) potential is normalized at the origin
without receiving a separate normalization premise for its physical
background correction. -/
theorem cmp102Eq80CorrectedPhysicalGlobalPotential_zero
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
    (D₃ : FinePhysicalOneCochain d L N' Nc →
      CoarsePhysicalOneCochain d N' Nc)
    (V₀ : FinePhysicalOneCochain d L N' Nc → ℝ)
    (Δπ : FinePhysicalOneCochain d L N' Nc →L[ℝ]
      FinePhysicalOneCochain d L N' Nc)
    (J : FinePhysicalOneCochain d L N' Nc)
    (hD₃0 : D₃ 0 = 0) (hV₀0 : V₀ 0 = 0) :
    cmp102Eq80CorrectedPhysicalGlobalPotential
      U ha hP hε hsmall hbudget ρ radius r s S hcontract
      D₃ V₀ Δπ J 0 = 0 := by
  unfold cmp102Eq80CorrectedPhysicalGlobalPotential
  exact cmp102Eq80PhysicalGlobalPotential_zero
    U ha hP hε hsmall hbudget
    (cmp102Eq80PhysicalBackgroundCorrection
      U ha hP hε hsmall hbudget ρ radius r s S hcontract)
    D₃ V₀ Δπ J
    (cmp102Eq80PhysicalBackgroundCorrection_zero
      U ha hP hε hsmall hbudget ρ radius r s S hcontract)
    hD₃0 hV₀0

end

end YangMills.RG
