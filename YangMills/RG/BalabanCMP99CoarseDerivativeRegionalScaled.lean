/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99CoarseDerivativeRegional
import YangMills.RG.BalabanCMP99SourceRetainedPhysicalPrecision

/-!
# Scale-correct regional CMP99 coarse-derivative control

CMP99 uses `D_U^eta = eta^-1 D_U`.  Applying the regional physical
`Ubar` estimate at consecutive spacings `eta` and `M eta` cancels the
unscaled factor `M^2` exactly.  This file records that cancellation before
the estimate is iterated in the multiscale Poincare argument.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- Exact conversion between the printed scaled derivative and the
unscaled covariant difference on the zero extension. -/
theorem norm_cmp99ActiveRegionSourceCovariantD0CLM_sq_eq
    (Omega : ActiveGaugeRegion d N')
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N' Nc)
    {spacing : ℝ} (hspacing : 0 < spacing)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    ‖cmp99ActiveRegionSourceCovariantD0CLM Omega rho U spacing phi‖ ^ 2 =
      spacing⁻¹ ^ 2 *
        ‖covariantD0CLM rho U (extendZeroZeroCLM Omega phi)‖ ^ 2 := by
  rw [cmp99ActiveRegionSourceCovariantD0CLM,
    ContinuousLinearMap.smul_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hspacing)]
  simp only [ContinuousLinearMap.comp_apply]
  ring

/-- Scale-correct physical one-step gradient recurrence.  The coarse
spacing `M * eta` cancels the unscaled `M^2`, leaving the exact source
counting factor `M^-d` in front of the fine derivative energy. -/
theorem norm_scaledCovariantD0_cmp99SourceRegionalAverage_physicalUbar_sq_le
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (background : GaugeConfig d (M * N') (SUN Nc))
    (weight epsilonFine spacing : ℝ)
    (epsilonFine_nonneg : 0 ≤ epsilonFine)
    (hspacing : 0 < spacing)
    (noWinding : cmp99SourceUbarFineDeviationRadius d M epsilonFine <
      cmp99UbarNoWindingThreshold Nc)
    (logSmall :
      cmp99UbarLogRadius
          (cmp99SourceUbarFineNoWindingBudget
            (d := d) (M := M) (Nc := Nc) epsilonFine noWinding) < 1)
    (fine_small : ∀ e : ConcreteEdge d (M * N'),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonFine)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    let data := cmp99SourceRegionalScaleDataOfFineSmall hd hM Omega background
      weight epsilonFine epsilonFine_nonneg noWinding fine_small
    let coarseOmega :=
      cmp99ActiveCoarseRegion (M := M) (N' := N') Omega
    let coarsePhi := cmp99SourceTransportedBlockAverageCLM Omega
      (cmp99SourceWeightedPhysicalTransport (matrixSUNAdjointModel Nc)
        background) phi
    ‖cmp99ActiveRegionSourceCovariantD0CLM coarseOmega
        (matrixSUNAdjointModel Nc) data.nextBackground
        ((M : ℝ) * spacing) coarsePhi‖ ^ 2 ≤
      2 * cmp99SourceBlockAverageWeight M d *
          ‖cmp99ActiveRegionSourceCovariantD0CLM Omega
            (matrixSUNAdjointModel Nc) background spacing phi‖ ^ 2 +
        (2 * cmp99SourceBlockAverageWeight M d *
          (2 * (cmp99SourceTripleHolonomyRadius d M epsilonFine +
            cmp99SourceUbarNextFineRadius d M epsilonFine)) ^ 2 * (d : ℝ) /
              (((M : ℝ) * spacing) ^ 2)) * ‖phi‖ ^ 2 := by
  dsimp only
  have hraw :=
    norm_covariantD0_cmp99SourceRegionalAverage_physicalUbar_sq_le
      hd hM Omega hOmega background weight epsilonFine
      epsilonFine_nonneg noWinding logSmall fine_small phi
  rw [norm_cmp99ActiveRegionSourceCovariantD0CLM_sq_eq
      _ _ _ (mul_pos (by exact_mod_cast (Nat.zero_lt_of_lt hM)) hspacing),
    norm_cmp99ActiveRegionSourceCovariantD0CLM_sq_eq
      Omega (matrixSUNAdjointModel Nc) background hspacing phi]
  have hscale : 0 ≤ (((M : ℝ) * spacing)⁻¹) ^ 2 := sq_nonneg _
  calc
    (((M : ℝ) * spacing)⁻¹) ^ 2 *
        ‖covariantD0CLM (matrixSUNAdjointModel Nc)
          (cmp99SourceRegionalScaleDataOfFineSmall hd hM Omega background
            weight epsilonFine epsilonFine_nonneg noWinding fine_small).nextBackground
          (extendZeroZeroCLM
            (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
            (cmp99SourceTransportedBlockAverageCLM Omega
              (cmp99SourceWeightedPhysicalTransport
                (matrixSUNAdjointModel Nc) background) phi))‖ ^ 2 ≤
      (((M : ℝ) * spacing)⁻¹) ^ 2 *
        (2 * (((M : ℝ) ^ d)⁻¹ * (M : ℝ) ^ 2) *
            ‖covariantD0CLM (matrixSUNAdjointModel Nc) background
              (extendZeroZeroCLM Omega phi)‖ ^ 2 +
          2 * (cmp99SourceBlockAverageWeight M d *
            (2 * (cmp99SourceTripleHolonomyRadius d M epsilonFine +
              cmp99SourceUbarNextFineRadius d M epsilonFine)) ^ 2 *
                (d : ℝ)) * ‖phi‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hraw hscale
    _ = 2 * cmp99SourceBlockAverageWeight M d *
          (spacing⁻¹ ^ 2 *
            ‖covariantD0CLM (matrixSUNAdjointModel Nc) background
              (extendZeroZeroCLM Omega phi)‖ ^ 2) +
        (2 * cmp99SourceBlockAverageWeight M d *
          (2 * (cmp99SourceTripleHolonomyRadius d M epsilonFine +
            cmp99SourceUbarNextFineRadius d M epsilonFine)) ^ 2 * (d : ℝ) /
              (((M : ℝ) * spacing) ^ 2)) * ‖phi‖ ^ 2 := by
      unfold cmp99SourceBlockAverageWeight
      have hM0 : (M : ℝ) ≠ 0 := by positivity
      have hs0 : spacing ≠ 0 := ne_of_gt hspacing
      field_simp

end

end YangMills.RG
