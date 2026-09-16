/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98SourceGAdSmallField
import YangMills.RG.BalabanCMP98ContourExponentialTransport
import YangMills.RG.BalabanCMP116WilsonBackgroundFactorBounds

/-!
# Source production of the CMP102 one-third background budget

The CMP102 logarithmic chart uses the bound

`‖D̄_b(x,0)‖ ≤ 1/3`.

This module derives it from the literal small-background assumption on
positive physical bonds.  Reverse-edge smallness is not supplied separately:
it follows from the gauge-configuration orientation law and unitarity.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- Positive-bond smallness controls every oriented physical link with the
same constant. -/
theorem norm_physicalGaugeBackground_apply_sub_one_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (ε : ℝ) (hsmall : PhysicalWilsonSmallBackground U ε)
    (e : ConcreteEdge d (M * N')) :
    ‖(U e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ ε := by
  rw [← cmp98OrientedBackgroundSUN_eq_apply U e,
    cmp98OrientedBackgroundSUN_coe]
  have h :=
    norm_orientedWilsonBackgroundFactor_sub_trivial_le U ε hsmall e
  rw [orientedWilsonBackgroundFactor_trivial] at h
  exact h

/-- The printed fine-link radius condition produces the complete CMP102
one-third background estimate on every coarse block. -/
theorem cmp102PhysicalBackgroundBase_of_small
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : PhysicalWilsonSmallBackground U ε)
    (hradius : cmp99SourceUbarFineDeviationRadius d M ε ≤ 1 / 3) :
    ∀ b : PhysicalBond d N', ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3 := by
  intro b x hx
  exact
    (norm_cmp98UbarAmbientDeviationMatrix_zero_le_fineRadius
      hd hM U ε hε
      (norm_physicalGaugeBackground_apply_sub_one_le U ε hsmall)
      b x hx).trans hradius

end

end YangMills.RG
