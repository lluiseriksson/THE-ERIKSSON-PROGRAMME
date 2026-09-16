/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatGeneratedComplexStencilDictionary
import YangMills.RG.BalabanCMP99SourceFlatGeneratedPrecisionScalarDictionary

/-!
# Generated active Laplacian in full-box complex coordinates

The retained active real field determines both its Dirichlet zero extension
and its transported full-box complex field.  At the canonical generated
spacing, this module combines the sealed regional compression, flat ambient
specialization, neighbour transport and scalar-spacing dictionary.  The
result is only the Laplacian summand of the literal full-complex precision.

No generated mass, full precision, inverse or Green equality is asserted.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

namespace CMP99SourceGeneratedTerminalComplexFieldData

/-- At every generated active target, the literal regional flat Laplacian at
the canonical spacing is the real form of the full-box complex stencil with
its exact generated block-side square.  The active field, both zero
extensions, background and spacing are fixed internally. -/
theorem activeLaplacian_complexification_eq_fullComplexStencil
    {Omega : ActiveGaugeRegion d N} {depth : ℕ}
    (D : CMP99SourceGeneratedTerminalComplexFieldData
      (M := M) (Nc := Nc) Omega depth)
    (target : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))) :
    let spacing := cmp99SourceGeneratedFullComplexSpacing M (depth + 1)
    let blockSide := cmp99SourceGeneratedFullComplexBlockSide M (depth + 1)
    cmp99SUNLieCoordComplexificationLM Nc
        (cmp99ActiveRegionSourceCovariantLaplacian
          (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
          (matrixSUNAdjointModel Nc)
          (cmp99SourceFlatGaugeConfig d
            (cmp99RegionalLatticeSize M N (depth + 1)) Nc)
          spacing D.activeField target) =
      ((blockSide : ℕ) : ℂ) ^ 2 •
        cmp99FlatPeriodicComplexFibreStencil D.complexZeroExtension
          (cmp99GeneratedFineBoxOneBlockEquiv
            (d := d) M N (depth + 1) target.1) := by
  dsimp only
  have hscalarReal :=
    cmp99SourceGeneratedFullComplexSpacing_inv_mul_inv M (depth + 1)
  have hscalarComplex :
      (((cmp99SourceGeneratedFullComplexSpacing M (depth + 1))⁻¹ : ℝ) : ℂ) *
          (((cmp99SourceGeneratedFullComplexSpacing M (depth + 1))⁻¹ : ℝ) : ℂ) =
        (((cmp99SourceGeneratedFullComplexBlockSide M (depth + 1) : ℕ) : ℂ)) ^ 2 := by
    exact_mod_cast hscalarReal
  rw [D.activeLaplacian_apply_eq_compression]
  change cmp99SUNLieCoordComplexificationLM Nc
      (cmp99GeneratedAmbientScaledCovariantLaplacian
        (matrixSUNAdjointModel Nc)
        (cmp99SourceFlatGaugeConfig d
          (cmp99RegionalLatticeSize M N (depth + 1)) Nc)
        (cmp99SourceGeneratedFullComplexSpacing M (depth + 1))
        D.realZeroExtension target.1) = _
  rw [D.generatedAmbientLaplacian_apply_eq_flatStencil]
  rw [map_smul, map_smul]
  rw [← D.complexStencil_apply_generatedBox_eq_complexification_realStencil]
  change
    (((cmp99SourceGeneratedFullComplexSpacing M (depth + 1))⁻¹ : ℝ) : ℂ) •
        ((((cmp99SourceGeneratedFullComplexSpacing M (depth + 1))⁻¹ : ℝ) : ℂ) •
          cmp99FlatPeriodicComplexFibreStencil D.complexZeroExtension
            (cmp99GeneratedFineBoxOneBlockEquiv
              (d := d) M N (depth + 1) target.1)) = _
  rw [smul_smul, hscalarComplex]

end CMP99SourceGeneratedTerminalComplexFieldData

end

end YangMills.RG
