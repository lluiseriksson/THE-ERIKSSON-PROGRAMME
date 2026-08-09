/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq249CentralStabilizedDenominatorVariation

/-!
# PRE-VALIDATION: central fine-symbol upper bound on the CMP89 strip

Source is present, its `.olean` has not yet been materialized, and the result
has not yet been verified by the compiler.

The complete stabilized endpoint numerator contains the central fine symbol
as a literal multiplier of the noncentral alias sum.  The existing source
development already bounds its vertical variation and its matching real
slice, but only as internal steps of the stabilized-denominator estimate.
This file exposes their exact sum as a reusable, scale-uniform upper bound.

No endpoint numerator, alias sum, contour integral, complete `B0`, physical
owner bound, window-15 conclusion or terminal field is produced here.
-/

namespace YangMills.RG

noncomputable section

/-- Explicit scale-uniform upper bound for the central fine symbol on the
complete CMP89 polydisc. -/
def cmp89Eq251CentralFineSymbolStripUpperBound (rho : ℝ) : ℝ :=
  cmp89Eq249CentralFineSymbolVerticalBound rho +
    cmp89Eq249CentralFineSymbolRealBound

/-- The central fine symbol is bounded on the complete polydisc by its
already sealed vertical budget plus its already sealed real-slice bound. -/
theorem norm_cmp89Eq249CentralEntireFineSymbol_le_stripUpperBound
    {L j : ℕ} [NeZero L] {mass rho : ℝ}
    (hmass : CMP89Eq251UniformMassWindow mass)
    (hrho : 0 ≤ rho)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho) :
    ‖cmp89Eq249CentralEntireFineSymbol 4 L j mass z‖ ≤
      cmp89Eq251CentralFineSymbolStripUpperBound rho := by
  let z0 : Fin 4 → ℂ := cmp89Eq245ComplexMomentumRealSlice z
  let delta := cmp89Eq249CentralEntireFineSymbol 4 L j mass z
  let delta0 := cmp89Eq249CentralEntireFineSymbol 4 L j mass z0
  obtain ⟨hxi, hxi1⟩ := cmp89Eq245_inverseScale_mem_Ioc L j
  have hz0 : z0 = fun mu => (p mu : ℂ) := by
    funext mu
    simp [z0, cmp89Eq245ComplexMomentumRealSlice, hreal mu]
  have hraw :=
    norm_cmp89Eq245EntireScaledLaplacianSymbol_sub_realSlice_le
      (d := 4) (xi := ((L : ℝ) ^ j)⁻¹) (mass := mass)
      hxi hxi1 hrho himag
  have hcube :=
    cmp89Eq245EntireScaledLaplacianVerticalBudget_le_centralBound
      hrho hp hreal
  have hvariation :
      ‖delta - delta0‖ ≤ cmp89Eq249CentralFineSymbolVerticalBound rho := by
    have hraw' :
        ‖delta - delta0‖ ≤
          cmp89Eq245EntireScaledLaplacianVerticalBudget 4 rho z := by
      simpa [delta, delta0, z0, cmp89Eq249CentralEntireFineSymbol]
        using hraw
    exact hraw'.trans hcube
  have hrealBound :
      ‖delta0‖ ≤ cmp89Eq249CentralFineSymbolRealBound := by
    change ‖cmp89Eq249CentralEntireFineSymbol 4 L j mass z0‖ ≤
      cmp89Eq249CentralFineSymbolRealBound
    rw [hz0]
    exact norm_cmp89Eq249CentralEntireFineSymbol_realSlice_le
      (L := L) (j := j) hmass hp
  calc
    ‖cmp89Eq249CentralEntireFineSymbol 4 L j mass z‖ = ‖delta‖ := rfl
    _ = ‖(delta - delta0) + delta0‖ := by
      congr 1
      ring
    _ ≤ ‖delta - delta0‖ + ‖delta0‖ := norm_add_le _ _
    _ ≤ cmp89Eq249CentralFineSymbolVerticalBound rho +
        cmp89Eq249CentralFineSymbolRealBound :=
      add_le_add hvariation hrealBound
    _ = cmp89Eq251CentralFineSymbolStripUpperBound rho := rfl

end

end YangMills.RG
