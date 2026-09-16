/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98Eq119NonlinearBridge

/-!
# Right-trivialized four-source bridge for CMP98 (119)

The literal nonlinear block `exp(Y) * C` has right variation

`g(ad (-Y)) (dY) + exp(Y) (dC * C⁻¹) exp(-Y)`.

This file inserts the already constructed four-contour formula for `dY`.
It deliberately keeps the older left-trivialized `g(ad Y)` endpoints
unchanged: identifying either frame with every printed convention in
CMP98 (119)--(124) requires the subsequent endpoint-conjugation dictionary.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- The four physical logarithmic sources transported by the outer operator
forced by literal right trivialization. -/
def cmp98Eq119RightFourSourcePhysicalVariation
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') : Matrix (Fin Nc) (Fin Nc) ℂ :=
  cmp98GAd (-(cmp98UbarLogAverage U b 0))
    (cmp98Eq124FourSourceGAdInvAverage U A b)

/-- The right four-source term is exactly the right exponential derivative
after the local one-third logarithmic bounds identify the physical
logarithmic variation. -/
theorem cmp98Eq119RightFourSourcePhysicalVariation_eq_logVariation
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hthird : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3) :
    cmp98Eq119RightFourSourcePhysicalVariation U A b =
      cmp98GAd (-(cmp98UbarLogAverage U b 0))
        (cmp98UbarLogAveragePhysicalVariation U A b) := by
  rw [cmp98Eq119RightFourSourcePhysicalVariation,
    cmp98UbarLogAveragePhysicalVariation_eq_fourSourceGAdInvAverage
      U A b hthird]

/-- **Physical four-source formula for the literal nonlinear right
variation.**  Both the outer sign and the direct coarse conjugation are
derived from the exact product curve; neither is supplied as a convention. -/
theorem cmp98Eq119NonlinearRightVariation_eq_fourSources_add_direct
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hthird : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3) :
    cmp98Eq119NonlinearRightVariation U A b =
      cmp98Eq119RightFourSourcePhysicalVariation U A b +
        cmp98Eq119DirectCoarseTransportedVariation U A b := by
  have hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1 := by
    intro x hx
    exact lt_of_le_of_lt (hthird x hx) (by norm_num)
  rw [cmp98Eq119NonlinearRightVariation_eq U A b hsmall,
    cmp98Eq119RightFourSourcePhysicalVariation_eq_logVariation
      U A b hthird]

end

end YangMills.RG
