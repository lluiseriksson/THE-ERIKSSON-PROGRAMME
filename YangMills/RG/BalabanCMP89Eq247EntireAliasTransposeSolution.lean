/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq246EntireAliasPrecisionMatrix

/-!
# Transposed alias-fibre solution in CMP89 (2.47)

The DFT convention of the physical weighted adjoint produces the printed
opposite-momentum row.  Consequently the finite system acts through the
transpose of the printed diagonal-plus-rank-one matrix.  This module proves
that action literally and constructs the quotient displayed in CMP89 (2.47)
as its solution wherever the individual fine symbols and the reduced alias
denominator are nonzero.

The nonvanishing assumptions describe only the domain of the printed
rational expression.  They are not promoted to terminal hypotheses: the
central removable zero and its stabilized continuation remain open here.
No interacting or regional transport, inverse CLM or physical `B0` is
claimed.
-/

namespace YangMills.RG

open Matrix

noncomputable section

/-- The literal CMP89 (2.47) alias solution in the row-source orientation. -/
def cmp89Eq247EntireAliasTransposeSolution
    (d L j : ℕ) (mass a : ℝ) (z : Fin d → ℂ) :
    CMP89Eq246AliasIndex d L j → ℂ :=
  fun m =>
    cmp89Eq246EntireAliasAverageRow d L j z m /
      (cmp89Eq246EntireAliasFineSymbol d L j mass z m *
        cmp89Eq247ComplexReducedAliasDenominator d L j mass a z)

/-- Transposing the printed alias matrix puts the opposite-momentum row on
the output axis and the direct-momentum column inside the contraction. -/
theorem cmp89Eq246EntireAliasPrecisionMatrix_transpose_mulVec
    (d L j : ℕ) (mass a : ℝ) (z : Fin d → ℂ)
    (phi : CMP89Eq246AliasIndex d L j → ℂ)
    (m : CMP89Eq246AliasIndex d L j) :
    (cmp89Eq246EntireAliasPrecisionMatrix d L j mass a z).transpose.mulVec
        phi m =
      cmp89Eq246EntireAliasFineSymbol d L j mass z m * phi m +
        (a : ℂ) * cmp89Eq246EntireAliasAverageRow d L j z m *
          ∑ n, cmp89Eq246EntireAliasAverageColumn d L j z n * phi n := by
  classical
  change (∑ x,
      cmp89Eq246EntireAliasPrecisionMatrix d L j mass a z x m * phi x) = _
  unfold cmp89Eq246EntireAliasPrecisionMatrix
  simp only [add_mul, Finset.sum_add_distrib]
  have hdiagonal :
      (∑ x,
        (if x = m then cmp89Eq246EntireAliasFineSymbol d L j mass z x else 0) *
          phi x) =
        cmp89Eq246EntireAliasFineSymbol d L j mass z m * phi m := by
    simpa only [ite_mul, zero_mul, eq_comm] using
      (Fintype.sum_ite_eq m
        (fun x => cmp89Eq246EntireAliasFineSymbol d L j mass z x * phi x))
  rw [hdiagonal]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- On the domain of the printed quotients, the internally defined (2.47)
vector solves the transposed alias system against the literal row source. -/
theorem cmp89Eq246EntireAliasPrecisionMatrix_transpose_mulVec_solution
    (d L j : ℕ) (mass a : ℝ) (z : Fin d → ℂ)
    (hfine : ∀ m : CMP89Eq246AliasIndex d L j,
      cmp89Eq246EntireAliasFineSymbol d L j mass z m ≠ 0)
    (hreduced : cmp89Eq247ComplexReducedAliasDenominator
      d L j mass a z ≠ 0) :
    (cmp89Eq246EntireAliasPrecisionMatrix d L j mass a z).transpose.mulVec
        (cmp89Eq247EntireAliasTransposeSolution d L j mass a z) =
      cmp89Eq246EntireAliasAverageRow d L j z := by
  classical
  let reduced := cmp89Eq247ComplexReducedAliasDenominator d L j mass a z
  let fine := cmp89Eq246EntireAliasFineSymbol d L j mass z
  let column := cmp89Eq246EntireAliasAverageColumn d L j z
  let row := cmp89Eq246EntireAliasAverageRow d L j z
  have hsumSubtype :
      (∑ n : CMP89Eq246AliasIndex d L j, column n * row n / fine n) =
        ∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
          cmp89Eq248ComplexAliasDenominatorSummand d L j mass z m := by
    rw [Finset.sum_subtype
      (cmp89Eq245CenteredAliasVectors d (L ^ j)) (fun _ => Iff.rfl)]
    apply Finset.sum_congr rfl
    intro m hm
    simp only [column, row, fine,
      cmp89Eq246EntireAliasAverageColumn,
      cmp89Eq246EntireAliasAverageRow,
      cmp89Eq246EntireAliasFineSymbol,
      cmp89Eq248ComplexAliasDenominatorSummand,
      cmp89Eq245EntireAveragePair]
  have hreducedEq :
      reduced = 1 + (a : ℂ) *
        ∑ n : CMP89Eq246AliasIndex d L j, column n * row n / fine n := by
    change cmp89Eq247ComplexReducedAliasDenominator d L j mass a z = _
    rw [cmp89Eq247ComplexReducedAliasDenominator, hsumSubtype]
  have hsolution (n : CMP89Eq246AliasIndex d L j) :
      cmp89Eq247EntireAliasTransposeSolution d L j mass a z n =
        row n / (fine n * reduced) := rfl
  have hsumSolution :
      (∑ n : CMP89Eq246AliasIndex d L j,
        column n *
          cmp89Eq247EntireAliasTransposeSolution d L j mass a z n) =
        (∑ n : CMP89Eq246AliasIndex d L j,
          column n * row n / fine n) / reduced := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n _
    rw [hsolution]
    field_simp [hfine n, hreduced]
  funext m
  rw [cmp89Eq246EntireAliasPrecisionMatrix_transpose_mulVec, hsumSolution,
    hsolution]
  have hfine' : fine m ≠ 0 := by
    simpa [fine] using hfine m
  have hreduced' : reduced ≠ 0 := by
    simpa [reduced] using hreduced
  have hfirst : fine m * (row m / (fine m * reduced)) = row m / reduced := by
    field_simp [hfine', hreduced']
  rw [hfirst]
  calc
    row m / reduced +
          (a : ℂ) * row m *
            ((∑ n : CMP89Eq246AliasIndex d L j,
              column n * row n / fine n) / reduced) =
        row m *
          (1 + (a : ℂ) *
            ∑ n : CMP89Eq246AliasIndex d L j,
              column n * row n / fine n) / reduced := by ring
    _ = row m := by
      rw [← hreducedEq]
      field_simp [hreduced']

end

end YangMills.RG
