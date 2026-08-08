/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq246EntireAliasPrecisionMatrix

/-!
# Central-pole cancellation in the CMP89 (2.47)--(2.49) alias denominator

PRE-VALIDATION: source is present, the `.olean` has not yet been materialized,
and these declarations have not yet been verified by the Lean compiler.

The solved formula (2.47) displays one quotient by each fine symbol
`Delta_l`.  The zero alias is different from the other aliases: its symbol can
approach zero with the running mass, while the block-averaging rank-one term
fills precisely that direction.  Multiplying the reduced denominator by the
central `Delta_0` exposes the cancellation

`Delta_0 + a*u_0*u_{-0} + a*Delta_0*sum_{l != 0} u_l*u_{-l}/Delta_l`.

This module defines that stabilized denominator and proves its exact equality
with `Delta_0` times the displayed rational denominator wherever the displayed
central quotient is defined.  The new expression extends across a zero of
`Delta_0`; it deliberately retains the noncentral quotients.  Their uniform
nonvanishing strip and the positive real lower bound for the stabilized
denominator remain subsequent quantitative obligations.

No strip radius, `B0`, contour displacement, or physical Green estimate is
claimed.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- The all-zero reciprocal alias. -/
def cmp89Eq249ZeroAlias (d : ℕ) : Fin d → ℤ := fun _ => 0

/-- The central fine-lattice symbol `Delta_0`. -/
def cmp89Eq249CentralEntireFineSymbol
    (d L j : ℕ) (mass : ℝ) (z : Fin d → ℂ) : ℂ :=
  cmp89Eq245EntireScaledLaplacianSymbol
    d (((L : ℝ) ^ j)⁻¹) mass z

/-- The central opposite-momentum averaging pair `u_0*u_{-0}`. -/
def cmp89Eq249CentralEntireAveragePair
    (d L j : ℕ) (z : Fin d → ℂ) : ℂ :=
  cmp89Eq245EntireAveragePair d (L ^ j) z

/-- The noncentral part of the rational alias sum in (2.47). -/
def cmp89Eq249ComplexNoncentralAliasSum
    (d L j : ℕ) (mass : ℝ) (z : Fin d → ℂ) : ℂ :=
  ∑ m ∈ (cmp89Eq245CenteredAliasVectors d (L ^ j)).erase
      (cmp89Eq249ZeroAlias d),
    cmp89Eq248ComplexAliasDenominatorSummand d L j mass z m

/-- The reduced denominator with the potentially removable central pole
cancelled before any complex lower bound is attempted. -/
def cmp89Eq249CentralStabilizedAliasDenominator
    (d L j : ℕ) (mass a : ℝ) (z : Fin d → ℂ) : ℂ :=
  cmp89Eq249CentralEntireFineSymbol d L j mass z +
    (a : ℂ) * cmp89Eq249CentralEntireAveragePair d L j z +
    (a : ℂ) * cmp89Eq249CentralEntireFineSymbol d L j mass z *
      cmp89Eq249ComplexNoncentralAliasSum d L j mass z

/-- The central alias belongs to the printed fibre whenever `L` is nonzero. -/
theorem cmp89Eq249ZeroAlias_mem
    (d L j : ℕ) [NeZero L] :
    cmp89Eq249ZeroAlias d ∈ cmp89Eq245CenteredAliasVectors d (L ^ j) := by
  simpa only [cmp89Eq249ZeroAlias] using
    zero_mem_cmp89Eq245CenteredAliasVectors_pow d L j

/-- The displayed rational alias sum splits exactly into its central and
noncentral branches. -/
theorem cmp89Eq247ComplexReducedAliasDenominator_eq_central_add_noncentral
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin d → ℂ) :
    cmp89Eq247ComplexReducedAliasDenominator d L j mass a z =
      1 + (a : ℂ) *
        (cmp89Eq249CentralEntireAveragePair d L j z /
            cmp89Eq249CentralEntireFineSymbol d L j mass z +
          cmp89Eq249ComplexNoncentralAliasSum d L j mass z) := by
  let aliases := cmp89Eq245CenteredAliasVectors d (L ^ j)
  let zeroAlias := cmp89Eq249ZeroAlias d
  let term := cmp89Eq248ComplexAliasDenominatorSummand d L j mass z
  have hzero : zeroAlias ∈ aliases := by
    exact cmp89Eq249ZeroAlias_mem d L j
  have hsplit := Finset.sum_erase_add aliases term hzero
  have halias :
      cmp89Eq248EntireAliasMomentum z zeroAlias = z := by
    funext mu
    simp [cmp89Eq248EntireAliasMomentum, zeroAlias,
      cmp89Eq249ZeroAlias, cmp89Eq245AliasShift]
  have hcentral :
      term zeroAlias =
        cmp89Eq249CentralEntireAveragePair d L j z /
          cmp89Eq249CentralEntireFineSymbol d L j mass z := by
    change
      cmp89Eq248ComplexAliasDenominatorSummand d L j mass z zeroAlias = _
    rw [cmp89Eq248ComplexAliasDenominatorSummand, halias]
    rfl
  rw [cmp89Eq247ComplexReducedAliasDenominator]
  change 1 + (a : ℂ) * (∑ m ∈ aliases, term m) = _
  rw [← hsplit, hcentral]
  rw [cmp89Eq249ComplexNoncentralAliasSum]
  change
    1 + (a : ℂ) *
        ((∑ m ∈ aliases.erase zeroAlias, term m) +
          cmp89Eq249CentralEntireAveragePair d L j z /
            cmp89Eq249CentralEntireFineSymbol d L j mass z) =
      1 + (a : ℂ) *
        (cmp89Eq249CentralEntireAveragePair d L j z /
            cmp89Eq249CentralEntireFineSymbol d L j mass z +
          ∑ m ∈ aliases.erase zeroAlias, term m)
  ring

/-- Exact cancellation of the central displayed quotient.  This theorem is
stated on the domain of the original rational formula; the stabilized right
side itself remains defined when `Delta_0 = 0`. -/
theorem cmp89Eq249CentralFine_mul_reduced_eq_stabilized
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin d → ℂ)
    (hcentral : cmp89Eq249CentralEntireFineSymbol d L j mass z ≠ 0) :
    cmp89Eq249CentralEntireFineSymbol d L j mass z *
        cmp89Eq247ComplexReducedAliasDenominator d L j mass a z =
      cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z := by
  rw [cmp89Eq247ComplexReducedAliasDenominator_eq_central_add_noncentral]
  rw [cmp89Eq249CentralStabilizedAliasDenominator]
  field_simp [hcentral]
  ring

end

end YangMills.RG
