/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalCorrectionLinearGrowth
import YangMills.RG.BalabanCMP102Eq80GlobalPotentialLinearGrowth

/-!
# First-order normalization of the physically corrected equation (80)

The physical fixed point is inserted into the global CMP102 potential without
postulating a Fréchet derivative for that fixed point.  A local scalar bound
on the explicit chart coefficient, together with the proved physical linear
estimate, is enough to obtain zero derivative of the complete potential.
-/

open scoped RealInnerProductSpace Topology

namespace YangMills.RG

open YangMills Filter

noncomputable section

variable {d L N' Nc : ℕ}
variable [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
  [NeZero (L * N')]

set_option maxHeartbeats 10000000 in
/-- **Physical first-order closure of equation (80).**  The implicit
background correction need not be differentiated.  The only additional
local input is a finite upper bound on its already explicit scalar growth
coefficient. -/
theorem cmp102Eq80CorrectedPhysicalGlobalPotential_hasFDerivAt_zero
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
    (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ᶠ A in 𝓝 0,
      cmp102Eq80PhysicalBackgroundCorrectionLinearGrowthConstant
        U ha hP hε hsmall hbudget ρ radius r s S A ≤ K)
    (hD₃0 : D₃ 0 = 0)
    (hD₃ : HasFDerivAt D₃
      (0 : FinePhysicalOneCochain d L N' Nc →L[ℝ]
        CoarsePhysicalOneCochain d N' Nc) 0)
    (hV₀ : HasFDerivAt V₀
      (0 : FinePhysicalOneCochain d L N' Nc →L[ℝ] ℝ) 0) :
    HasFDerivAt
      (cmp102Eq80CorrectedPhysicalGlobalPotential
        U ha hP hε hsmall hbudget ρ radius r s S hcontract
        D₃ V₀ Δπ J)
      (0 : FinePhysicalOneCochain d L N' Nc →L[ℝ] ℝ) 0 := by
  let D :=
    cmp102Eq80PhysicalBackgroundCorrection
      U ha hP hε hsmall hbudget ρ radius r s S hcontract
  have hDgrowth : ∀ᶠ A in 𝓝 0, ‖D A‖ ≤ K * ‖A‖ := by
    filter_upwards [hK] with A hKA
    exact
      (norm_cmp102Eq80PhysicalBackgroundCorrection_le
        U ha hP hε hsmall hbudget ρ radius r s S hcontract A).trans
        (mul_le_mul_of_nonneg_right hKA (norm_nonneg A))
  unfold cmp102Eq80CorrectedPhysicalGlobalPotential
  exact cmp102Eq80GlobalPotential_hasFDerivAt_zero_of_linearGrowth
    D D₃ V₀
    (cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget)
    Δπ J K hK0
    (cmp102Eq80PhysicalBackgroundCorrection_zero
      U ha hP hε hsmall hbudget ρ radius r s S hcontract)
    hD₃0 hDgrowth hD₃ hV₀

end

end YangMills.RG
