/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalBackgroundCorrectionChoiceIndependence
import YangMills.RG.BalabanCMP102PhysicalIntrinsicCorrectionAnalytic

/-!
# Intrinsic fixed-point equation for the CMP102 correction

The Banach construction uses scalar chart packages to certify a ball.  The
map whose fixed point is selected, however, is the intrinsic equation-(122)
correction.  This file removes the packages from the equation and from its
uniqueness statement.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d L N' Nc : ℕ}
variable [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
  [NeZero (L * N')]

/-- The certificate-free physical fixed-point map
`D ↦ C_intrinsic(A - H D)` in the source sup norm. -/
noncomputable def cmp102IntrinsicPhysicalBackgroundCorrectionMap
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (A : FinePhysicalOneCochain d L N' Nc)
    (D : PhysicalGaugeOneCochainSup d N' Nc) :
    PhysicalGaugeOneCochainSup d N' Nc :=
  physicalGaugeOneCochainSupEquiv
    (cmp102IntrinsicPhysicalNonlinearCorrection U
      (A - cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget
        (physicalGaugeOneCochainSupEquiv.symm D)))

/-- On every certified ball, the Banach map is literally the intrinsic map.
The chart proof is consumed only to establish the open Mercator domain. -/
theorem cmp102PhysicalBackgroundCorrectionMap_eq_intrinsic_of_mem
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (A : FinePhysicalOneCochain d L N' Nc)
    (ρ r s : ℝ)
    (B : CMP102PhysicalBackgroundCorrectionBallData
      U ha hP hε hsmall hbudget A ρ r s)
    (D : PhysicalGaugeOneCochainSup d N' Nc)
    (hD : ‖D‖ ≤ ρ) :
    cmp102PhysicalBackgroundCorrectionMap
        U ha hP hε hsmall hbudget A ρ r s B D =
      cmp102IntrinsicPhysicalBackgroundCorrectionMap
        U ha hP hε hsmall hbudget A D := by
  rw [B.correctionMap_eq_of_mem D hD]
  unfold cmp102IntrinsicPhysicalBackgroundCorrectionMap
  congr 1
  apply cmp102PhysicalNonlinearCorrectionOfBudget_eq_intrinsic
  intro b x hx
  exact ((B.chartBudget D hD).base b x hx).trans_lt (by norm_num)

/-- The selected physical correction satisfies the certificate-free literal
fixed-point equation. -/
theorem cmp102Eq80PhysicalBackgroundCorrection_intrinsicEquation
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
    cmp102IntrinsicPhysicalBackgroundCorrectionMap
        U ha hP hε hsmall hbudget A
        (physicalGaugeOneCochainSupEquiv
          (cmp102Eq80PhysicalBackgroundCorrection
            U ha hP hε hsmall hbudget ρ radius r s S hcontract A)) =
      physicalGaugeOneCochainSupEquiv
        (cmp102Eq80PhysicalBackgroundCorrection
          U ha hP hε hsmall hbudget ρ radius r s S hcontract A) := by
  let D : PhysicalGaugeOneCochainSup d N' Nc :=
    Classical.choose ((S A).existsUnique_backgroundCorrection
      (hcontract A))
  have hspec :=
    Classical.choose_spec ((S A).existsUnique_backgroundCorrection
      (hcontract A))
  have hmap :=
    cmp102PhysicalBackgroundCorrectionMap_eq_intrinsic_of_mem
      U ha hP hε hsmall hbudget A (ρ A) (r A) (s A)
      (S A).toBallData D hspec.1.1
  have hfix :
      cmp102IntrinsicPhysicalBackgroundCorrectionMap
          U ha hP hε hsmall hbudget A D = D := by
    rw [← hmap]
    exact hspec.1.2
  simpa [D, cmp102Eq80PhysicalBackgroundCorrection] using hfix

/-- Uniqueness of the intrinsic fixed point on the source-certified ball. -/
theorem cmp102IntrinsicPhysicalBackgroundCorrectionMap_fixedPoint_unique
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (A : FinePhysicalOneCochain d L N' Nc)
    (ρ r s : ℝ)
    (B : CMP102PhysicalBackgroundCorrectionBallData
      U ha hP hε hsmall hbudget A ρ r s)
    (hcontract : B.contractionRate < 1)
    (D E : PhysicalGaugeOneCochainSup d N' Nc)
    (hD : ‖D‖ ≤ ρ) (hE : ‖E‖ ≤ ρ)
    (hfixD :
      cmp102IntrinsicPhysicalBackgroundCorrectionMap
        U ha hP hε hsmall hbudget A D = D)
    (hfixE :
      cmp102IntrinsicPhysicalBackgroundCorrectionMap
        U ha hP hε hsmall hbudget A E = E) :
    D = E := by
  rcases B.existsUnique_backgroundCorrection hcontract with
    ⟨F, _, hunique⟩
  have hcertD :
      cmp102PhysicalBackgroundCorrectionMap
          U ha hP hε hsmall hbudget A ρ r s B D = D := by
    rw [cmp102PhysicalBackgroundCorrectionMap_eq_intrinsic_of_mem
      U ha hP hε hsmall hbudget A ρ r s B D hD]
    exact hfixD
  have hcertE :
      cmp102PhysicalBackgroundCorrectionMap
          U ha hP hε hsmall hbudget A ρ r s B E = E := by
    rw [cmp102PhysicalBackgroundCorrectionMap_eq_intrinsic_of_mem
      U ha hP hε hsmall hbudget A ρ r s B E hE]
    exact hfixE
  exact (hunique D ⟨hD, hcertD⟩).trans
    (hunique E ⟨hE, hcertE⟩).symm

end

end YangMills.RG
