/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceRetainedPhysicalTower

/-!
# Transport of retained CMP99 physical coordinates

The literal source recursion transports its retained tail across the proved
equality between the active coarse region and the preceding iterated lift.
The physical coordinate family itself is independent of that outer regional
index.  This file records the exact transport law needed by later rectangular
kernel identifications.
-/

namespace YangMills.RG

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero N] [NeZero Nc]

/-- Transporting a retained tower between propositionally equal regions does
not change its physical coordinate type. -/
theorem CMP99SourceRetainedPhysicalTower.levelSite_transport
    {rho : SUNAdjointModel Nc}
    {Omega₁ Omega₂ : ActiveGaugeRegion d N}
    (h : Omega₁ = Omega₂) {spacing : ℝ}
    {background : GaugeConfig d N (SUN Nc)} {depth : ℕ}
    (T : CMP99SourceRetainedPhysicalTower rho Omega₂ M spacing background depth)
    (r : Fin (depth + 1)) :
    ((h.symm ▸ T).levelSite r) = T.levelSite r := by
  cases h
  rfl

end

end YangMills.RG
