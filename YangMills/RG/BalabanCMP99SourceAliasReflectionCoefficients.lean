/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatQprimePhysicalAliasPrecisionMatrix
import YangMills.RG.BalabanCMP99SourceSignedAliasFourierNegCarry

/-!
# Alias-reflection transport of the CMP89 fibre coefficients

The printed centered alias carrier is half open, so reflection is residue
negation rather than literal integer negation.  This file first proves the
exact replacement: at reflected alias and opposite base momentum, the alias
momentum is the negative original momentum plus an internally constructed
integer multiple of the genuine `2*pi*M` alias period.  The already sealed
period laws then transport the averaging column to the row, the row to the
column, and the fine symbol to itself.

This is coefficient algebra only.  It does not identify the stabilized
denominator or solution, reindex the physical cross-fibre sum, claim that the
zero alias is preserved termwise, construct a Brillouin integral or regional
`B0`, attain window 15, discharge a terminal field or inhabit `TermSource`.
-/

namespace YangMills.RG

noncomputable section

/-- The entire opposite-momentum Laplacian pairing is even. -/
theorem cmp89Eq245EntireScaledLaplacianSymbol_neg
    (d : ℕ) (xi mass : ℝ) (z : Fin d → ℂ) :
    cmp89Eq245EntireScaledLaplacianSymbol d xi mass (-z) =
      cmp89Eq245EntireScaledLaplacianSymbol d xi mass z := by
  unfold cmp89Eq245EntireScaledLaplacianSymbol
  congr 1
  apply Finset.sum_congr rfl
  intro mu _
  simp only [Pi.neg_apply, neg_neg]
  ring

/-- Opposite base momentum and the actual half-open carrier reflection give
the negative alias momentum up to coordinatewise integer alias periods. -/
theorem cmp89Eq248EntireAliasMomentum_aliasIndexOneReflection
    {d M : ℕ} [NeZero M] (z : Fin d → ℂ)
    (m : CMP89Eq246AliasIndex d M 1) :
    ∃ w : Fin d → ℤ,
      cmp89Eq248EntireAliasMomentum (-z)
          (cmp99SourceAliasIndexOneReflection d M m).1 =
        fun mu =>
          -cmp89Eq248EntireAliasMomentum z m.1 mu +
            (w mu : ℂ) * (((2 * Real.pi * (M : ℝ) : ℝ) : ℂ)) := by
  have hdiv : ∀ mu : Fin d, (M : ℤ) ∣
      (cmp99SourceAliasIndexOneReflection d M m).1 mu + m.1 mu := by
    intro mu
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [cmp99SourceAliasIndexOneReflection_coordinate_cast_eq_neg]
    ring
  choose w hw using hdiv
  refine ⟨w, ?_⟩
  funext mu
  have hwC := congrArg (fun x : ℤ => (x : ℂ)) (hw mu)
  push_cast at hwC
  simp only [cmp89Eq248EntireAliasMomentum, cmp89Eq245AliasShift,
    Pi.neg_apply]
  push_cast
  ring_nf at hwC ⊢
  linear_combination (2 * (Real.pi : ℂ)) * hwC

/-- Reflection exchanges the direct-momentum averaging column with the
opposite-momentum row. -/
theorem cmp89Eq246EntireAliasAverageColumn_neg_reflection_eq_row
    {d M : ℕ} [NeZero M] (z : Fin d → ℂ)
    (m : CMP89Eq246AliasIndex d M 1) :
    cmp89Eq246EntireAliasAverageColumn d M 1 (-z)
        (cmp99SourceAliasIndexOneReflection d M m) =
      cmp89Eq246EntireAliasAverageRow d M 1 z m := by
  rcases cmp89Eq248EntireAliasMomentum_aliasIndexOneReflection z m with
    ⟨w, hw⟩
  unfold cmp89Eq246EntireAliasAverageColumn
    cmp89Eq246EntireAliasAverageRow
  rw [hw]
  simpa only [pow_one] using
    cmp89Eq245EntireAverageAmplitude_add_int_aliasPeriods
      (Nat.pos_of_ne_zero (NeZero.ne M))
      (-cmp89Eq248EntireAliasMomentum z m.1) w

/-- The same reflection exchanges the opposite-momentum row with the direct
column. -/
theorem cmp89Eq246EntireAliasAverageRow_neg_reflection_eq_column
    {d M : ℕ} [NeZero M] (z : Fin d → ℂ)
    (m : CMP89Eq246AliasIndex d M 1) :
    cmp89Eq246EntireAliasAverageRow d M 1 (-z)
        (cmp99SourceAliasIndexOneReflection d M m) =
      cmp89Eq246EntireAliasAverageColumn d M 1 z m := by
  rcases cmp89Eq248EntireAliasMomentum_aliasIndexOneReflection z m with
    ⟨w, hw⟩
  have hneg :
      -cmp89Eq248EntireAliasMomentum (-z)
          (cmp99SourceAliasIndexOneReflection d M m).1 =
        fun mu =>
          cmp89Eq248EntireAliasMomentum z m.1 mu +
            ((-w mu : ℤ) : ℂ) *
              (((2 * Real.pi * (M : ℝ) : ℝ) : ℂ)) := by
    funext mu
    simp only [Pi.neg_apply]
    rw [congrFun hw mu]
    push_cast
    ring
  unfold cmp89Eq246EntireAliasAverageRow
    cmp89Eq246EntireAliasAverageColumn
  rw [hneg]
  simpa only [pow_one] using
    cmp89Eq245EntireAverageAmplitude_add_int_aliasPeriods
      (Nat.pos_of_ne_zero (NeZero.ne M))
      (cmp89Eq248EntireAliasMomentum z m.1) (fun mu => -w mu)

/-- The fine diagonal symbol is invariant under opposite base momentum and
the actual half-open alias reflection. -/
theorem cmp89Eq246EntireAliasFineSymbol_neg_reflection_eq
    {d M : ℕ} [NeZero M] (mass : ℝ) (z : Fin d → ℂ)
    (m : CMP89Eq246AliasIndex d M 1) :
    cmp89Eq246EntireAliasFineSymbol d M 1 mass (-z)
        (cmp99SourceAliasIndexOneReflection d M m) =
      cmp89Eq246EntireAliasFineSymbol d M 1 mass z m := by
  rcases cmp89Eq248EntireAliasMomentum_aliasIndexOneReflection z m with
    ⟨w, hw⟩
  unfold cmp89Eq246EntireAliasFineSymbol
  simp only [pow_one]
  rw [hw]
  rw [show
    cmp89Eq245EntireScaledLaplacianSymbol d ((M : ℝ)⁻¹) mass
        (fun mu =>
          -cmp89Eq248EntireAliasMomentum z m.1 mu +
            (w mu : ℂ) * (((2 * Real.pi * (M : ℝ) : ℝ) : ℂ))) =
      cmp89Eq245EntireScaledLaplacianSymbol d ((M : ℝ)⁻¹) mass
        (-cmp89Eq248EntireAliasMomentum z m.1) by
          exact cmp89Eq245EntireScaledLaplacianSymbol_add_int_aliasPeriods
            (Nat.pos_of_ne_zero (NeZero.ne M)) mass
            (-cmp89Eq248EntireAliasMomentum z m.1) w]
  exact cmp89Eq245EntireScaledLaplacianSymbol_neg
    d ((M : ℝ)⁻¹) mass (cmp89Eq248EntireAliasMomentum z m.1)

end

end YangMills.RG
