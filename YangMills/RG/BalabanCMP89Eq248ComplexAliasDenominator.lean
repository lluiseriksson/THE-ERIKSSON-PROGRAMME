/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq248EntireFourierSymbols
import YangMills.RG.BalabanCMP89Eq250FullDenominatorLower
import YangMills.RG.BalabanCMP89Eq251EntireAverageAliasDictionary

/-!
# Complex alias denominator in CMP89 (2.47)--(2.49)

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result is not compiler-verified.

CMP89 (2.47) contains the reciprocal of

`1 + a_j * sum_l |u_j(p+l)|^2 / Delta^xi(p+l)`.

For complex momentum, the squared norm is replaced by the already sealed
opposite-momentum pairing `u(z+l) * u(-z-l)`.  This module assembles that
literal finite alias denominator and the version in (2.49), obtained after
multiplication by `Delta^1(z)`.  It proves that the latter recovers the
already sealed real denominator exactly on the printed alias set.

The individual quotients are analytic wherever their fine-lattice
denominators do not vanish.  No uniform complex nonvanishing strip, explicit
strip radius, contour displacement, or regional-Green estimate is claimed.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- Complex momentum translated by one reciprocal-lattice alias. -/
def cmp89Eq248EntireAliasMomentum
    {d : ℕ} (z : Fin d → ℂ) (m : Fin d → ℤ) : Fin d → ℂ :=
  fun mu => z mu + (cmp89Eq245AliasShift m mu : ℂ)

/-- One literal complex alias summand in the denominator of CMP89 (2.47). -/
def cmp89Eq248ComplexAliasDenominatorSummand
    (d L j : ℕ) (mass : ℝ) (z : Fin d → ℂ) (m : Fin d → ℤ) : ℂ :=
  cmp89Eq245EntireAveragePair d (L ^ j)
      (cmp89Eq248EntireAliasMomentum z m) /
    cmp89Eq245EntireScaledLaplacianSymbol
      d (((L : ℝ) ^ j)⁻¹) mass (cmp89Eq248EntireAliasMomentum z m)

/-- The denominator in CMP89 (2.47), before multiplication by the unit-lattice
symbol. -/
def cmp89Eq247ComplexReducedAliasDenominator
    (d L j : ℕ) (mass a : ℝ) (z : Fin d → ℂ) : ℂ :=
  1 + (a : ℂ) *
    ∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
      cmp89Eq248ComplexAliasDenominatorSummand d L j mass z m

/-- Entire continuation of the unit-lattice symbol `Delta^1`. -/
def cmp89Eq249EntireUnitLaplacianSymbol
    (d : ℕ) (mass : ℝ) (z : Fin d → ℂ) : ℂ :=
  cmp89Eq245EntireScaledLaplacianSymbol d 1 mass z

/-- The complete denominator in CMP89 (2.49), after multiplication by
`Delta^1(z)`. -/
def cmp89Eq249ComplexFullAliasDenominator
    (d L j : ℕ) (mass a : ℝ) (z : Fin d → ℂ) : ℂ :=
  cmp89Eq247ComplexReducedAliasDenominator d L j mass a z *
    cmp89Eq249EntireUnitLaplacianSymbol d mass z

/-- At real momentum, the scaled symbol with unit spacing is exactly the
literal unit-lattice symbol used in CMP89 (2.49). -/
theorem cmp89Eq245ScaledLaplacianSymbol_one_eq_unit
    (d : ℕ) (mass : ℝ) (p : Fin d → ℝ) :
    cmp89Eq245ScaledLaplacianSymbol d 1 mass p =
      cmp89Eq249UnitLaplacianSymbol d mass p := by
  simp [cmp89Eq245ScaledLaplacianSymbol,
    cmp89Eq249UnitLaplacianSymbol,
    cmp89Eq245ScaledDifferenceNorm,
    cmp89Eq249UnitDifferenceNorm]

/-- The entire unit-lattice symbol recovers the literal nonnegative symbol on
the real slice. -/
theorem cmp89Eq249EntireUnitLaplacianSymbol_ofReal_eq
    (d : ℕ) (mass : ℝ) (p : Fin d → ℝ) :
    cmp89Eq249EntireUnitLaplacianSymbol d mass (fun mu => (p mu : ℂ)) =
      (cmp89Eq249UnitLaplacianSymbol d mass p : ℂ) := by
  rw [cmp89Eq249EntireUnitLaplacianSymbol,
    cmp89Eq245EntireScaledLaplacianSymbol_ofReal_eq,
    cmp89Eq245ScaledLaplacianSymbol_one_eq_unit]

/-- One complex alias summand agrees exactly with the literal real summand on
every alias printed in CMP89 (2.45). -/
theorem cmp89Eq248ComplexAliasDenominatorSummand_ofReal_eq
    {d L j : ℕ} [NeZero L] {mass : ℝ} {p : Fin d → ℝ}
    {m : Fin d → ℤ}
    (hm : m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j))
    (hp : ∀ mu, |p mu| ≤ Real.pi) :
    cmp89Eq248ComplexAliasDenominatorSummand d L j mass
        (fun mu => (p mu : ℂ)) m =
      (cmp89Eq250AliasDenominatorSummand
        d (((L : ℝ) ^ j)⁻¹) mass p m : ℂ) := by
  have hN : 0 < L ^ j :=
    pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  have halias :
      cmp89Eq248EntireAliasMomentum (fun mu => (p mu : ℂ)) m =
        fun mu => ((p mu + cmp89Eq245AliasShift m mu : ℝ) : ℂ) := by
    funext mu
    simp [cmp89Eq248EntireAliasMomentum]
  rw [cmp89Eq248ComplexAliasDenominatorSummand]
  rw [halias]
  rw [cmp89Eq245EntireAveragePair_ofReal_eq,
    cmp89Eq245EntireScaledLaplacianSymbol_ofReal_eq]
  simp only [cmp89Eq245AliasShift]
  rw [cmp89Eq245EntireAverageAmplitude_ofReal_scaled_alias_eq hN hm hp]
  rw [cmp89Eq250AliasDenominatorSummand]
  simp only [cmp89Eq245AliasShift]
  push_cast
  ring

/-- Exact real-slice dictionary for the complete multiplied denominator in
CMP89 (2.49)--(2.50). -/
theorem cmp89Eq249ComplexFullAliasDenominator_ofReal_eq
    {d L j : ℕ} [NeZero L] {mass a : ℝ} {p : Fin d → ℝ}
    (hp : ∀ mu, |p mu| ≤ Real.pi) :
    cmp89Eq249ComplexFullAliasDenominator d L j mass a
        (fun mu => (p mu : ℂ)) =
      (cmp89Eq250FullAliasDenominator d L j mass a p : ℂ) := by
  have hsum :
      (∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
          cmp89Eq248ComplexAliasDenominatorSummand d L j mass
            (fun mu => (p mu : ℂ)) m) =
        ((∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
          cmp89Eq250AliasDenominatorSummand
            d (((L : ℝ) ^ j)⁻¹) mass p m : ℝ) : ℂ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro m hm
    exact cmp89Eq248ComplexAliasDenominatorSummand_ofReal_eq hm hp
  rw [cmp89Eq249ComplexFullAliasDenominator,
    cmp89Eq247ComplexReducedAliasDenominator, hsum,
    cmp89Eq249EntireUnitLaplacianSymbol_ofReal_eq,
    cmp89Eq250FullAliasDenominator]
  push_cast
  ring

end

end YangMills.RG
