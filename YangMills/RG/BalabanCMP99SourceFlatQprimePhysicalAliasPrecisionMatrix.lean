/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatQprimeComplexFibreModeAction
import YangMills.RG.BalabanCMP99SourceFlatQprimeSignedAliasMomentumDictionary

/-!
# PRE-VALIDATION: physical flat Qprime alias precision matrix

Source is present at this checkpoint, but its `.olean` has not yet been
materialized and the result has not yet been verified by the compiler.

At fixed coarse momentum the fine modes form one finite reciprocal fibre.
This module keeps the two physical momentum orientations distinct: the
opposite-momentum factor performs fibre analysis and the direct factor
performs synthesis.  Their literal composition is the rank-one term in
CMP89 (2.46).  The diagonal term is the rescaled periodic flat stencil, not
an unrelated free diagonal.

The signed carrier equivalence is then used on both matrix axes.  The result
is the exact entire diagonal-plus-rank-one matrix already printed in CMP89.
No abstract adjointness is used to exchange row and column, and the two
budgets remain separate in the definition.

Honest scope: this is the finite flat Fourier-fibre identity.  It does not
yet identify the active-region real CLM with the fibre analysis/synthesis,
construct the inverse, or transport it to the regional Green operator.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped BigOperators

noncomputable section

/-- A scaled difference at spacing `M^-1` absorbs one literal factor `M`
from its momentum. -/
theorem cmp89Eq245EntireScaledDifference_invNat_natMul
    {M : ℕ} [NeZero M] (z : ℂ) :
    cmp89Eq245EntireScaledDifference ((M : ℝ)⁻¹) ((M : ℂ) * z) =
      (M : ℂ) * cmp89Eq245EntireScaledDifference 1 z := by
  have hM : (M : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne M)
  unfold cmp89Eq245EntireScaledDifference
  push_cast
  have hcancel : (M : ℂ)⁻¹ * ((M : ℂ) * z) = z := by
    field_simp [hM]
  rw [hcancel]
  norm_num
  field_simp [hM]

/-- The scaled entire fine symbol is invariant under every coordinatewise
integer multiple of its exact `2*pi*M` reciprocal period. -/
theorem cmp89Eq245EntireScaledLaplacianSymbol_add_int_aliasPeriods
    {d M : ℕ} (hM : 0 < M) (mass : ℝ)
    (z : Fin d → ℂ) (w : Fin d → ℤ) :
    cmp89Eq245EntireScaledLaplacianSymbol d ((M : ℝ)⁻¹) mass
        (fun mu => z mu + (w mu : ℂ) *
          (((2 * Real.pi * (M : ℝ) : ℝ) : ℂ))) =
      cmp89Eq245EntireScaledLaplacianSymbol d ((M : ℝ)⁻¹) mass z := by
  unfold cmp89Eq245EntireScaledLaplacianSymbol
  congr 1
  apply Finset.sum_congr rfl
  intro mu _
  have hp := cmp89Eq245EntireAverageBase_add_int_aliasPeriod
    hM (w mu) (z mu)
  have hn := cmp89Eq245EntireAverageBase_add_int_aliasPeriod
    hM (-w mu) (-z mu)
  unfold cmp89Eq245EntireAverageBase at hp hn
  push_cast at hp hn
  have hneg :
      -(z mu + (w mu : ℂ) * (2 * (Real.pi : ℂ) * (M : ℂ))) =
        -z mu + ((-w mu : ℤ) : ℂ) *
          (2 * (Real.pi : ℂ) * (M : ℂ)) := by
    push_cast
    ring
  unfold cmp89Eq245EntireScaledDifference
  push_cast
  rw [hneg, hp, hn]

/-- The physical rescaled diagonal on a fine periodic Fourier mode.  The
factor `M^2` is the spacing conversion; the mass is added exactly once. -/
def cmp99SourceFlatQprimeRescaledPeriodicFineSymbol
    {d M N' : ℕ} [NeZero M] [NeZero N']
    (mass : ℝ) (k : FinBox d (M * N')) : ℂ :=
  (M : ℂ) ^ 2 * cmp99FlatPeriodicLaplacianSymbol k + (mass : ℂ) ^ 2

/-- The literal scaled entire symbol evaluated at the physical signed
one-block momentum. -/
def cmp99SourceFlatQprimePhysicalFineSymbol
    {d M N' : ℕ} [NeZero M] [NeZero N']
    (mass : ℝ) (k : FinBox d (M * N')) : ℂ :=
  cmp89Eq245EntireScaledLaplacianSymbol d ((M : ℝ)⁻¹) mass
    (cmp99SourceFlatQprimeAmplitudeMomentum k)

/-- The physical signed-momentum symbol is exactly the rescaled periodic
stencil eigenvalue, including the mass term. -/
theorem cmp99SourceFlatQprimePhysicalFineSymbol_eq_rescaledPeriodic
    {d M N' : ℕ} [NeZero M] [NeZero N']
    (mass : ℝ) (k : FinBox d (M * N')) :
    cmp99SourceFlatQprimePhysicalFineSymbol mass k =
      cmp99SourceFlatQprimeRescaledPeriodicFineSymbol mass k := by
  unfold cmp99SourceFlatQprimePhysicalFineSymbol
    cmp99SourceFlatQprimeRescaledPeriodicFineSymbol
    cmp89Eq245EntireScaledLaplacianSymbol
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro mu _
  simp only [cmp99SourceFlatQprimeAmplitudeMomentum]
  rw [show -((M : ℂ) * (cmp99FlatDiscreteMomentum k mu : ℂ)) =
      (M : ℂ) * (-(cmp99FlatDiscreteMomentum k mu : ℂ)) by ring,
    show -(-((M : ℂ) * (cmp99FlatDiscreteMomentum k mu : ℂ))) =
      (M : ℂ) * (cmp99FlatDiscreteMomentum k mu : ℂ) by ring]
  rw [cmp89Eq245EntireScaledDifference_invNat_natMul,
    cmp89Eq245EntireScaledDifference_invNat_natMul,
    cmp99Flat_characterPair_eq_entireUnitDifferencePair]
  ring

/-- Fixed-coarse physical fine-momentum fibre. -/
abbrev CMP99SourceFlatQprimeFixedCoarseFibre
    (d M N' : ℕ) [NeZero M] [NeZero N'] (ell : FinBox d N') :=
  {k : FinBox d (M * N') // cmp99SourceFlatQprimeCoarseAlias k = ell}

/-- Opposite-momentum fibre analysis factor.  This orientation is explicit;
it is not inferred from self-adjointness. -/
def cmp99SourceFlatQprimePhysicalFibreAnalysis
    {d M N' : ℕ} [NeZero M] [NeZero N'] (ell : FinBox d N')
    (phi : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell → ℂ) : ℂ :=
  ∑ n, cmp89Eq245EntireAverageAmplitude d M
      (-cmp99SourceFlatQprimeAmplitudeMomentum n.1) * phi n

/-- Direct-momentum fibre synthesis factor. -/
def cmp99SourceFlatQprimePhysicalFibreSynthesis
    {d M N' : ℕ} [NeZero M] [NeZero N'] (ell : FinBox d N')
    (eta : ℂ) (m : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell) : ℂ :=
  cmp89Eq245EntireAverageAmplitude d M
      (cmp99SourceFlatQprimeAmplitudeMomentum m.1) * eta

/-- Literal physical rank-one fibre matrix.  The row and column factors are
kept separate in the definition. -/
def cmp99SourceFlatQprimePhysicalRankOneMatrix
    {d M N' : ℕ} [NeZero M] [NeZero N'] (ell : FinBox d N') :
    Matrix (CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell)
      (CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell) ℂ :=
  fun m n =>
    cmp89Eq245EntireAverageAmplitude d M
        (cmp99SourceFlatQprimeAmplitudeMomentum m.1) *
      cmp89Eq245EntireAverageAmplitude d M
        (-cmp99SourceFlatQprimeAmplitudeMomentum n.1)

/-- The rank-one matrix action is literally synthesis after analysis. -/
theorem cmp99SourceFlatQprimePhysicalRankOneMatrix_mulVec
    {d M N' : ℕ} [NeZero M] [NeZero N'] (ell : FinBox d N')
    (phi : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell → ℂ)
    (m : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell) :
    (cmp99SourceFlatQprimePhysicalRankOneMatrix ell).mulVec phi m =
      cmp99SourceFlatQprimePhysicalFibreSynthesis ell
        (cmp99SourceFlatQprimePhysicalFibreAnalysis ell phi) m := by
  unfold cmp99SourceFlatQprimePhysicalRankOneMatrix Matrix.mulVec dotProduct
    cmp99SourceFlatQprimePhysicalFibreSynthesis
    cmp99SourceFlatQprimePhysicalFibreAnalysis
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- Literal physical diagonal-plus-rank-one precision on the fixed coarse
fibre.  `a` multiplies only the rank-one block term. -/
def cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix
    {d M N' : ℕ} [NeZero M] [NeZero N'] (ell : FinBox d N')
    (mass a : ℝ) :
    Matrix (CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell)
      (CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell) ℂ :=
  fun m n =>
    (if m = n then cmp99SourceFlatQprimePhysicalFineSymbol mass m.1 else 0) +
      (a : ℂ) * cmp99SourceFlatQprimePhysicalRankOneMatrix ell m n

/-- Each physical diagonal entry transports to the printed CMP89 fine
symbol under the signed alias dictionary. -/
theorem cmp99SourceFlatQprimePhysicalFineSymbol_eq_entireAliasFineSymbol
    {d M N' : ℕ} [NeZero M] [NeZero N'] (ell : FinBox d N')
    (mass : ℝ) (k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell) :
    cmp99SourceFlatQprimePhysicalFineSymbol mass k.1 =
      cmp89Eq246EntireAliasFineSymbol d M 1 mass
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
        (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
          d M N' ell k) := by
  rcases cmp99SourceFlatQprimeAmplitudeMomentum_eq_alias_add_period ell k with
    ⟨w, hw⟩
  unfold cmp99SourceFlatQprimePhysicalFineSymbol
    cmp89Eq246EntireAliasFineSymbol
  rw [hw]
  simpa only [pow_one] using
    cmp89Eq245EntireScaledLaplacianSymbol_add_int_aliasPeriods
      (Nat.pos_of_ne_zero (NeZero.ne M)) mass
      (cmp89Eq248EntireAliasMomentum
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
        (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
          d M N' ell k).1) w

/-- Entrywise physical-to-printed dictionary.  Equality of diagonal indices
is transported only through injectivity of the signed equivalence. -/
theorem cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix_entry_eq_cmp89
    {d M N' : ℕ} [NeZero M] [NeZero N'] (ell : FinBox d N')
    (mass a : ℝ)
    (m n : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell) :
    cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix ell mass a m n =
      cmp89Eq246EntireAliasPrecisionMatrix d M 1 mass a
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
        (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
          d M N' ell m)
        (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
          d M N' ell n) := by
  rw [cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix,
    cmp89Eq246EntireAliasPrecisionMatrix,
    cmp99SourceFlatQprimePhysicalRankOneMatrix,
    cmp99SourceFlatQprimePhysicalFineSymbol_eq_entireAliasFineSymbol,
    cmp99SourceFlatQprimeAmplitude_eq_entireAliasColumn,
    cmp99SourceFlatQprimeNegAmplitude_eq_entireAliasRow]
  by_cases hmn : m = n
  · subst n
    simp
  · have halias :
        cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv d M N' ell m ≠
          cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv d M N' ell n :=
      fun h => hmn
        ((cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
          d M N' ell).injective h)
    simp [hmn, halias]

/-- Reindexing both axes by the signed physical dictionary gives the literal
CMP89 entire alias precision matrix. -/
theorem cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix_reindexed_eq_cmp89
    {d M N' : ℕ} [NeZero M] [NeZero N'] (ell : FinBox d N')
    (mass a : ℝ) :
    (fun m n : CMP89Eq246AliasIndex d M 1 =>
      cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix ell mass a
        ((cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
          d M N' ell).symm m)
        ((cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
          d M N' ell).symm n)) =
      cmp89Eq246EntireAliasPrecisionMatrix d M 1 mass a
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell) := by
  funext m n
  simpa using
    cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix_entry_eq_cmp89
      ell mass a
      ((cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
        d M N' ell).symm m)
      ((cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
        d M N' ell).symm n)

end

end YangMills.RG
