/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatGeneratedBackgroundDictionary

/-!
# Flat generated ambient Laplacian

PRE-VALIDATION: source present; `.olean` not yet materialized; result not yet
verified by the compiler.

For the canonical real zero extension retained by the generated terminal field
package, this module specializes the literal ambient covariant Laplacian at the
source-recursion flat background.  The independently named unit backgrounds
are related by the sealed dictionary; they are not identified by caller data.

No shift transport, complex stencil, spacing-power dictionary, mass summand,
full precision, inverse or Green operator is asserted here.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

namespace CMP99SourceGeneratedTerminalComplexFieldData

/-- The ambient generated Laplacian on the canonical real zero extension at
the literal source flat background is exactly the scaled flat periodic
stencil.  The field and both backgrounds are fixed internally. -/
theorem generatedAmbientLaplacian_apply_eq_flatStencil
    {Omega : ActiveGaugeRegion d N} {depth : ℕ}
    (D : CMP99SourceGeneratedTerminalComplexFieldData
      (M := M) (Nc := Nc) Omega depth)
    (rho : SUNAdjointModel Nc) (spacing : ℝ)
    (x : FinBox d (cmp99RegionalLatticeSize M N (depth + 1))) :
    cmp99GeneratedAmbientScaledCovariantLaplacian rho
        (cmp99SourceFlatGaugeConfig d
          (cmp99RegionalLatticeSize M N (depth + 1)) Nc)
        spacing D.realZeroExtension x =
      spacing⁻¹ • spacing⁻¹ •
        cmp99FlatPeriodicLaplacianStencil D.realZeroExtension x := by
  rw [cmp99SourceFlatGaugeConfig_eq_cmp99FlatGaugeBackground]
  exact cmp99GeneratedAmbientScaledCovariantLaplacian_one_apply
    rho spacing D.realZeroExtension x

end CMP99SourceGeneratedTerminalComplexFieldData

end

end YangMills.RG
