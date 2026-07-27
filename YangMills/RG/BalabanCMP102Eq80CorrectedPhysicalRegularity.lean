/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalCorrectionRegularity
import YangMills.RG.BalabanCMP102Eq80PhysicalH

/-!
# Regularity of the physically corrected equation-(80) potential

The implicit background correction is the source-defined fixed point and
its smoothness is now produced internally.  Consequently the regularity
interface for the corrected potential mentions only the remaining literal
source functions `D₃` and `V₀`.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d L N' Nc : ℕ}
variable [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
  [NeZero (L * N')]

/-- Smooth regularity of the corrected physical equation-(80) potential,
with no regularity premise for its implicit correction. -/
theorem contDiff_top_cmp102Eq80CorrectedPhysicalGlobalPotential
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
    (D₃ : FinePhysicalOneCochain d L N' Nc →
      CoarsePhysicalOneCochain d N' Nc)
    (V₀ : FinePhysicalOneCochain d L N' Nc → ℝ)
    (Δπ : FinePhysicalOneCochain d L N' Nc →L[ℝ]
      FinePhysicalOneCochain d L N' Nc)
    (J : FinePhysicalOneCochain d L N' Nc)
    (hD₃ : ContDiff ℝ ⊤ D₃) (hV₀ : ContDiff ℝ ⊤ V₀) :
    ContDiff ℝ ⊤
      (cmp102Eq80CorrectedPhysicalGlobalPotential
        U ha hP hε hsmall hbudget ρ radius
          (fun _ => r) (fun _ => s) S hcontract D₃ V₀ Δπ J) := by
  unfold cmp102Eq80CorrectedPhysicalGlobalPotential
  exact
    contDiff_top_cmp102Eq80PhysicalGlobalPotential
      U ha hP hε hsmall hbudget
      (cmp102Eq80PhysicalBackgroundCorrection
        U ha hP hε hsmall hbudget ρ radius
          (fun _ => r) (fun _ => s) S hcontract)
      D₃ V₀ Δπ J
      (contDiff_top_cmp102Eq80PhysicalBackgroundCorrection
        U ha hP hε hsmall hbudget ρ radius r s S hρ hcontract)
      hD₃ hV₀

/-- `C²` specialization consumed by the radial Taylor operator. -/
theorem contDiff_two_cmp102Eq80CorrectedPhysicalGlobalPotential
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
    (D₃ : FinePhysicalOneCochain d L N' Nc →
      CoarsePhysicalOneCochain d N' Nc)
    (V₀ : FinePhysicalOneCochain d L N' Nc → ℝ)
    (Δπ : FinePhysicalOneCochain d L N' Nc →L[ℝ]
      FinePhysicalOneCochain d L N' Nc)
    (J : FinePhysicalOneCochain d L N' Nc)
    (hD₃ : ContDiff ℝ ⊤ D₃) (hV₀ : ContDiff ℝ ⊤ V₀) :
    ContDiff ℝ 2
      (cmp102Eq80CorrectedPhysicalGlobalPotential
        U ha hP hε hsmall hbudget ρ radius
          (fun _ => r) (fun _ => s) S hcontract D₃ V₀ Δπ J) :=
  (contDiff_top_cmp102Eq80CorrectedPhysicalGlobalPotential
    U ha hP hε hsmall hbudget ρ radius r s S hρ hcontract
      D₃ V₀ Δπ J hD₃ hV₀).of_le le_top

end

end YangMills.RG
