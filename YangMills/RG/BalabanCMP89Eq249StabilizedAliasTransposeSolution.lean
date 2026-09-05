/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq247EntireAliasTransposeSolution
import YangMills.RG.BalabanCMP89Eq249CentralStabilizedAliasDenominator

/-!
# Central-stabilized transposed alias solution

The rational CMP89 (2.47) solution divides every alias by its fine symbol.
That presentation has a removable central zero.  Here the zero alias is
separated before solving the diagonal-plus-rank-one system: the central
coefficient is divided only by the already sealed stabilized denominator,
while every noncentral coefficient retains its literal fine-symbol quotient.

The resulting vector is proved to solve the transposed entire alias matrix.
Only the noncentral fine symbols and the stabilized denominator are required
to be nonzero.  In particular no nonvanishing assumption is imposed on the
central fine symbol.  This is the algebraic stabilization required before the
physical field construction can cross the removable zero.
-/

namespace YangMills.RG

open Matrix

noncomputable section

/-- The zero reciprocal alias as an element of the finite alias fibre. -/
def cmp89Eq249CentralAliasIndex
    (d L j : ℕ) [NeZero L] : CMP89Eq246AliasIndex d L j :=
  ⟨cmp89Eq249ZeroAlias d,
    zero_mem_cmp89Eq245CenteredAliasVectors_pow d L j⟩

@[simp]
theorem cmp89Eq249CentralAliasIndex_val
    (d L j : ℕ) [NeZero L] :
    (cmp89Eq249CentralAliasIndex d L j).1 = cmp89Eq249ZeroAlias d := rfl

/-- The transposed alias solution after cancelling the removable central
fine-symbol zero. -/
def cmp89Eq249StabilizedAliasTransposeSolution
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin d → ℂ) :
    CMP89Eq246AliasIndex d L j → ℂ :=
  fun m =>
    if m = cmp89Eq249CentralAliasIndex d L j then
      cmp89Eq246EntireAliasAverageRow d L j z m /
        cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z
    else
      cmp89Eq249CentralEntireFineSymbol d L j mass z *
          cmp89Eq246EntireAliasAverageRow d L j z m /
        (cmp89Eq246EntireAliasFineSymbol d L j mass z m *
          cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z)

@[simp]
theorem cmp89Eq249StabilizedAliasTransposeSolution_central
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin d → ℂ) :
    cmp89Eq249StabilizedAliasTransposeSolution d L j mass a z
        (cmp89Eq249CentralAliasIndex d L j) =
      cmp89Eq246EntireAliasAverageRow d L j z
          (cmp89Eq249CentralAliasIndex d L j) /
        cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z := by
  simp [cmp89Eq249StabilizedAliasTransposeSolution]

theorem cmp89Eq249StabilizedAliasTransposeSolution_noncentral
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin d → ℂ)
    (m : CMP89Eq246AliasIndex d L j)
    (hm : m ≠ cmp89Eq249CentralAliasIndex d L j) :
    cmp89Eq249StabilizedAliasTransposeSolution d L j mass a z m =
      cmp89Eq249CentralEntireFineSymbol d L j mass z *
          cmp89Eq246EntireAliasAverageRow d L j z m /
        (cmp89Eq246EntireAliasFineSymbol d L j mass z m *
          cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z) := by
  simp [cmp89Eq249StabilizedAliasTransposeSolution, hm]

/-- The noncentral subtype sum used by the matrix action is exactly the
printed noncentral alias sum.  No enumeration of the alias fibre is supplied. -/
theorem cmp89Eq249AliasSubtypeNoncentralSum_eq
    (d L j : ℕ) [NeZero L] (mass : ℝ) (z : Fin d → ℂ) :
    (∑ n ∈ (Finset.univ.erase (cmp89Eq249CentralAliasIndex d L j)),
        cmp89Eq246EntireAliasAverageColumn d L j z n *
            cmp89Eq246EntireAliasAverageRow d L j z n /
          cmp89Eq246EntireAliasFineSymbol d L j mass z n) =
      cmp89Eq249ComplexNoncentralAliasSum d L j mass z := by
  classical
  let aliases := cmp89Eq245CenteredAliasVectors d (L ^ j)
  let zeroAlias := cmp89Eq249ZeroAlias d
  let central := cmp89Eq249CentralAliasIndex d L j
  let subtypeTerm := fun n : CMP89Eq246AliasIndex d L j =>
    cmp89Eq246EntireAliasAverageColumn d L j z n *
        cmp89Eq246EntireAliasAverageRow d L j z n /
      cmp89Eq246EntireAliasFineSymbol d L j mass z n
  let printedTerm := cmp89Eq248ComplexAliasDenominatorSummand d L j mass z
  have hzero : zeroAlias ∈ aliases := cmp89Eq249ZeroAlias_mem d L j
  have hfull :
      (∑ n : CMP89Eq246AliasIndex d L j, subtypeTerm n) =
        ∑ m ∈ aliases, printedTerm m := by
    rw [Finset.sum_subtype aliases (fun _ => Iff.rfl)]
    apply Finset.sum_congr rfl
    intro m hm
    simp only [subtypeTerm, printedTerm,
      cmp89Eq246EntireAliasAverageColumn,
      cmp89Eq246EntireAliasAverageRow,
      cmp89Eq246EntireAliasFineSymbol,
      cmp89Eq248ComplexAliasDenominatorSummand,
      cmp89Eq245EntireAveragePair]
  have hcentral : subtypeTerm central = printedTerm zeroAlias := by
    simp [subtypeTerm, printedTerm, central, zeroAlias,
      cmp89Eq246EntireAliasAverageColumn,
      cmp89Eq246EntireAliasAverageRow,
      cmp89Eq246EntireAliasFineSymbol,
      cmp89Eq248ComplexAliasDenominatorSummand,
      cmp89Eq245EntireAveragePair]
  have hleft := Finset.sum_erase_add Finset.univ subtypeTerm
    (Finset.mem_univ central)
  have hright := Finset.sum_erase_add aliases printedTerm hzero
  change (∑ n ∈ Finset.univ.erase central, subtypeTerm n) = _
  rw [cmp89Eq249ComplexNoncentralAliasSum]
  change _ = ∑ m ∈ aliases.erase zeroAlias, printedTerm m
  calc
    (∑ n ∈ Finset.univ.erase central, subtypeTerm n) =
        (∑ n, subtypeTerm n) - subtypeTerm central := by
      rw [← hleft]
      ring
    _ = (∑ m ∈ aliases, printedTerm m) - printedTerm zeroAlias := by
      rw [hfull, hcentral]
    _ = ∑ m ∈ aliases.erase zeroAlias, printedTerm m := by
      rw [← hright]
      ring

/-- The central-stabilized vector solves the transposed entire alias system.
The central fine symbol is allowed to vanish; only noncentral fine symbols and
the stabilized denominator are required to be nonzero. -/
theorem cmp89Eq246EntireAliasPrecisionMatrix_transpose_mulVec_stabilizedSolution
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin d → ℂ)
    (hfine : ∀ m : CMP89Eq246AliasIndex d L j,
      m ≠ cmp89Eq249CentralAliasIndex d L j →
        cmp89Eq246EntireAliasFineSymbol d L j mass z m ≠ 0)
    (hstabilized :
      cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z ≠ 0) :
    (cmp89Eq246EntireAliasPrecisionMatrix d L j mass a z).transpose.mulVec
        (cmp89Eq249StabilizedAliasTransposeSolution d L j mass a z) =
      cmp89Eq246EntireAliasAverageRow d L j z := by
  classical
  let central := cmp89Eq249CentralAliasIndex d L j
  let fine := cmp89Eq246EntireAliasFineSymbol d L j mass z
  let column := cmp89Eq246EntireAliasAverageColumn d L j z
  let row := cmp89Eq246EntireAliasAverageRow d L j z
  let centralFine := cmp89Eq249CentralEntireFineSymbol d L j mass z
  let centralPair := cmp89Eq249CentralEntireAveragePair d L j z
  let noncentral := cmp89Eq249ComplexNoncentralAliasSum d L j mass z
  let stabilized :=
    cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z
  let solution := cmp89Eq249StabilizedAliasTransposeSolution d L j mass a z
  have hzeroMomentum :
      cmp89Eq248EntireAliasMomentum z (cmp89Eq249ZeroAlias d) = z := by
    funext mu
    simp [cmp89Eq248EntireAliasMomentum, cmp89Eq249ZeroAlias,
      cmp89Eq245AliasShift]
  have hcentralFine : fine central = centralFine := by
    change cmp89Eq245EntireScaledLaplacianSymbol
        d (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z (cmp89Eq249ZeroAlias d)) =
      cmp89Eq245EntireScaledLaplacianSymbol
        d (((L : ℝ) ^ j)⁻¹) mass z
    rw [hzeroMomentum]
  have hcentralPair : column central * row central = centralPair := by
    change cmp89Eq245EntireAverageAmplitude d (L ^ j)
          (cmp89Eq248EntireAliasMomentum z (cmp89Eq249ZeroAlias d)) *
        cmp89Eq245EntireAverageAmplitude d (L ^ j)
          (-cmp89Eq248EntireAliasMomentum z (cmp89Eq249ZeroAlias d)) =
      cmp89Eq245EntireAverageAmplitude d (L ^ j) z *
        cmp89Eq245EntireAverageAmplitude d (L ^ j) (-z)
    rw [hzeroMomentum]
  have hnoncentral :
      (∑ n ∈ Finset.univ.erase central,
        column n * row n / fine n) = noncentral := by
    exact cmp89Eq249AliasSubtypeNoncentralSum_eq d L j mass z
  have hstabilizedEq :
      stabilized =
        centralFine + (a : ℂ) * centralPair +
          (a : ℂ) * centralFine * noncentral := rfl
  have hstabilized' : stabilized ≠ 0 := by
    simpa only [stabilized] using hstabilized
  have hnoncentralSolution :
      (∑ n ∈ Finset.univ.erase central, column n * solution n) =
        centralFine * noncentral / stabilized := by
    calc
      (∑ n ∈ Finset.univ.erase central, column n * solution n) =
          ∑ n ∈ Finset.univ.erase central,
            centralFine * (column n * row n / fine n) / stabilized := by
        apply Finset.sum_congr rfl
        intro n hn
        have hncentral : n ≠ central := (Finset.mem_erase.mp hn).1
        have hsolutionN :
            solution n = centralFine * row n / (fine n * stabilized) := by
          simpa only [solution, centralFine, row, fine, stabilized, central]
            using cmp89Eq249StabilizedAliasTransposeSolution_noncentral
              d L j mass a z n hncentral
        rw [hsolutionN]
        have hfn : fine n ≠ 0 := hfine n hncentral
        change column n *
            (centralFine * row n / (fine n * stabilized)) = _
        field_simp [hfn, hstabilized']
      _ = centralFine *
          (∑ n ∈ Finset.univ.erase central,
            column n * row n / fine n) / stabilized := by
        rw [← Finset.sum_div, ← Finset.mul_sum]
      _ = centralFine * noncentral / stabilized := by
        rw [hnoncentral]
  have hsumSolution :
      (∑ n, column n * solution n) =
        (centralPair + centralFine * noncentral) / stabilized := by
    rw [← Finset.sum_erase_add Finset.univ
      (fun n => column n * solution n) (Finset.mem_univ central)]
    rw [hnoncentralSolution]
    have hcentralSolution :
        solution central = row central / stabilized := by
      simpa only [solution, row, stabilized, central] using
        cmp89Eq249StabilizedAliasTransposeSolution_central
          d L j mass a z
    rw [hcentralSolution]
    field_simp [hstabilized']
    rw [hcentralPair]
    ring
  funext m
  rw [cmp89Eq246EntireAliasPrecisionMatrix_transpose_mulVec, hsumSolution]
  change fine m * solution m +
      (a : ℂ) * row m *
        ((centralPair + centralFine * noncentral) / stabilized) = row m
  by_cases hm : m = central
  · subst m
    have hcentralSolution :
        solution central = row central / stabilized := by
      simpa only [solution, row, stabilized, central] using
        cmp89Eq249StabilizedAliasTransposeSolution_central
          d L j mass a z
    rw [hcentralSolution, hcentralFine]
    field_simp [hstabilized']
    rw [hstabilizedEq]
    ring
  · have hsolution :
        solution m = centralFine * row m / (fine m * stabilized) := by
      simpa only [solution, centralFine, row, fine, stabilized, central] using
        cmp89Eq249StabilizedAliasTransposeSolution_noncentral
          d L j mass a z m hm
    have hfm : fine m ≠ 0 := hfine m hm
    rw [hsolution]
    field_simp [hfm, hstabilized']
    rw [hstabilizedEq]
    ring

end

end YangMills.RG
