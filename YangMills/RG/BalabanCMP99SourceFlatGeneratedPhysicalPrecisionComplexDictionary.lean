/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatGeneratedActiveLaplacianComplexDictionary
import YangMills.RG.BalabanCMP99SourceFlatGeneratedQprimeMassComplexFieldDictionary
import YangMills.RG.BalabanCMP99SourceGeneratedFlatPhysicalPrecisionKernel

/-!
# Generated flat physical precision in full-box complex coordinates

PRE-VALIDATION: source present; `.olean` not yet materialized; result not yet
verified by the compiler.

The generated flat physical precision is already a literal sum of the active
covariant Laplacian and the generated counting-space `Q'^*Q'` mass.  This
module keeps those two summands separate until it consumes their independently
sealed complex dictionaries, then recognizes the exact full-box complex
precision with scalar mass fixed internally to zero.

No equality between caller-supplied operators is accepted.  No inverse or
Green equality is asserted.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

namespace CMP99SourceGeneratedTerminalComplexFieldData

/-- At every generated active target, the complexification of the literal
generated flat physical precision at canonical spacing is the corresponding
full-box complex precision action.  The active field, its two zero extensions,
the spacing, the generated averaging coefficient and scalar mass zero are all
fixed internally. -/
theorem physicalPrecision_complexification_eq_fullComplexAction
    {Omega : ActiveGaugeRegion d N} {depth : ℕ}
    (D : CMP99SourceGeneratedTerminalComplexFieldData
      (M := M) (Nc := Nc) Omega depth)
    (target : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))) :
    let spacing := cmp99SourceGeneratedFullComplexSpacing M (depth + 1)
    let a := cmp99SourceGeneratedFullComplexA
      d M (depth + 1) spacing 0
    let targetBox := cmp99GeneratedFineBoxOneBlockEquiv
      (d := d) M N (depth + 1) target.1
    cmp99SUNLieCoordComplexificationLM Nc
        (cmp99SourceGeneratedFlatPhysicalPrecisionExplicit
          (d := d) (M := M) (N := N) (Nc := Nc) Omega depth spacing
          D.activeField target) =
      cmp99SourceFlatFullComplexPrecisionAction
        (M := M ^ (depth + 1)) (N' := N) 0 a
        D.complexZeroExtension targetBox := by
  dsimp only
  unfold cmp99SourceGeneratedFlatPhysicalPrecisionExplicit
  unfold cmp99SourceGaugePrecision
  rw [ContinuousLinearMap.add_apply, PiLp.add_apply, map_add]
  rw [ContinuousLinearMap.smul_apply, PiLp.smul_apply]
  rw [D.activeLaplacian_complexification_eq_fullComplexStencil]
  rw [cmp99SourceGeneratedCountingMass_complexFieldDictionary]
  simp [cmp99SourceFlatFullComplexPrecisionAction,
    cmp99SourceGeneratedFullComplexBlockSide, complexZeroExtension]

end CMP99SourceGeneratedTerminalComplexFieldData

end

end YangMills.RG
