/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq246StabilizedAliasFullSolution

/-!
# Arbitrary-source solution of the transposed CMP89 (2.46) fibre

This module swaps the printed column/row roles in the already sealed complete
alias solution and keeps the central removable singularity cancelled before
division. The central branch is constructed from the exact column moment, so
the theorem proves the literal transposed matrix equation rather than
appealing to abstract self-adjointness.

-/

namespace YangMills.RG

open Matrix

noncomputable section

/-- Nonvanishing of the named central averaging pair forces the column gate
used by the transposed complete solution. -/
theorem cmp89Eq246CentralAverageColumn_ne_zero_of_pair_ne_zero
    (d L j : ℕ) [NeZero L] (z : Fin d → ℂ)
    (hpair : cmp89Eq249CentralEntireAveragePair d L j z ≠ 0) :
    cmp89Eq246EntireAliasAverageColumn d L j z
        (cmp89Eq249CentralAliasIndex d L j) ≠ 0 := by
  have hzeroMomentum :
      cmp89Eq248EntireAliasMomentum z (cmp89Eq249ZeroAlias d) = z := by
    funext mu
    simp [cmp89Eq248EntireAliasMomentum, cmp89Eq249ZeroAlias,
      cmp89Eq245AliasShift]
  have hproduct :
      cmp89Eq246EntireAliasAverageColumn d L j z
          (cmp89Eq249CentralAliasIndex d L j) *
        cmp89Eq246EntireAliasAverageRow d L j z
          (cmp89Eq249CentralAliasIndex d L j) =
        cmp89Eq249CentralEntireAveragePair d L j z := by
    change cmp89Eq245EntireAverageAmplitude d (L ^ j)
          (cmp89Eq248EntireAliasMomentum z (cmp89Eq249ZeroAlias d)) *
        cmp89Eq245EntireAverageAmplitude d (L ^ j)
          (-cmp89Eq248EntireAliasMomentum z (cmp89Eq249ZeroAlias d)) =
      cmp89Eq245EntireAverageAmplitude d (L ^ j) z *
        cmp89Eq245EntireAverageAmplitude d (L ^ j) (-z)
    rw [hzeroMomentum]
  intro hcolumn
  apply hpair
  rw [← hproduct, hcolumn, zero_mul]

/-- The noncentral column moment of an arbitrary fine source. -/
def cmp89Eq246StabilizedAliasTransposeNoncentralSourceMoment
    (d L j : ℕ) [NeZero L] (mass : ℝ) (z : Fin d → ℂ)
    (source : CMP89Eq246AliasIndex d L j → ℂ) : ℂ :=
  ∑ n ∈ Finset.univ.erase (cmp89Eq249CentralAliasIndex d L j),
    cmp89Eq246EntireAliasAverageColumn d L j z n * source n /
      cmp89Eq246EntireAliasFineSymbol d L j mass z n

/-- The exact column moment of the stabilized transposed solution. -/
def cmp89Eq246StabilizedAliasTransposeFullSolutionMoment
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin d → ℂ)
    (source : CMP89Eq246AliasIndex d L j → ℂ) : ℂ :=
  let central := cmp89Eq249CentralAliasIndex d L j
  let fine := cmp89Eq246EntireAliasFineSymbol d L j mass z
  let column := cmp89Eq246EntireAliasAverageColumn d L j z
  (column central * source central +
      fine central *
        cmp89Eq246StabilizedAliasTransposeNoncentralSourceMoment
          d L j mass z source) /
    cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z

/-- The complete arbitrary-source solution of the transposed alias matrix. -/
def cmp89Eq246StabilizedAliasTransposeFullSolution
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin d → ℂ)
    (source : CMP89Eq246AliasIndex d L j → ℂ) :
    CMP89Eq246AliasIndex d L j → ℂ :=
  let central := cmp89Eq249CentralAliasIndex d L j
  let fine := cmp89Eq246EntireAliasFineSymbol d L j mass z
  let column := cmp89Eq246EntireAliasAverageColumn d L j z
  let row := cmp89Eq246EntireAliasAverageRow d L j z
  let moment :=
    cmp89Eq246StabilizedAliasTransposeFullSolutionMoment
      d L j mass a z source
  fun m =>
    if m = central then
      (moment -
          ∑ n ∈ Finset.univ.erase central,
            column n *
              (source n / fine n -
                (a : ℂ) * row n * moment / fine n)) /
        column central
    else
      source m / fine m - (a : ℂ) * row m * moment / fine m

/-- By construction, the complete column moment is the named scalar moment. -/
theorem sum_column_mul_cmp89Eq246StabilizedAliasTransposeFullSolution_eq
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin d → ℂ)
    (source : CMP89Eq246AliasIndex d L j → ℂ)
    (hcolumn : cmp89Eq246EntireAliasAverageColumn d L j z
        (cmp89Eq249CentralAliasIndex d L j) ≠ 0) :
    (∑ n, cmp89Eq246EntireAliasAverageColumn d L j z n *
        cmp89Eq246StabilizedAliasTransposeFullSolution
          d L j mass a z source n) =
      cmp89Eq246StabilizedAliasTransposeFullSolutionMoment
        d L j mass a z source := by
  classical
  let central := cmp89Eq249CentralAliasIndex d L j
  let fine := cmp89Eq246EntireAliasFineSymbol d L j mass z
  let column := cmp89Eq246EntireAliasAverageColumn d L j z
  let row := cmp89Eq246EntireAliasAverageRow d L j z
  let moment :=
    cmp89Eq246StabilizedAliasTransposeFullSolutionMoment
      d L j mass a z source
  let noncentralSolution := fun n : CMP89Eq246AliasIndex d L j =>
    source n / fine n - (a : ℂ) * row n * moment / fine n
  rw [← Finset.sum_erase_add Finset.univ
    (fun n => column n *
      cmp89Eq246StabilizedAliasTransposeFullSolution
        d L j mass a z source n)
    (Finset.mem_univ central)]
  have hcentral :
      cmp89Eq246StabilizedAliasTransposeFullSolution
          d L j mass a z source central =
        (moment - ∑ n ∈ Finset.univ.erase central,
          column n * noncentralSolution n) / column central := by
    simp [cmp89Eq246StabilizedAliasTransposeFullSolution, central, fine,
      column, row, moment, noncentralSolution]
  rw [hcentral]
  have hnoncentral :
      (∑ n ∈ Finset.univ.erase central,
        column n * cmp89Eq246StabilizedAliasTransposeFullSolution
          d L j mass a z source n) =
        ∑ n ∈ Finset.univ.erase central,
          column n * noncentralSolution n := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnc : n ≠ central := (Finset.mem_erase.mp hn).1
    simp [cmp89Eq246StabilizedAliasTransposeFullSolution, central, fine,
      column, row, moment, noncentralSolution, hnc]
  rw [hnoncentral]
  rw [← mul_div_assoc, mul_div_cancel_left₀ _ hcolumn]
  ring

/-- The internally constructed vector solves the transposed literal alias
matrix for an arbitrary fine source. -/
theorem cmp89Eq246EntireAliasPrecisionMatrix_transpose_mulVec_stabilizedFullSolution
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin d → ℂ)
    (source : CMP89Eq246AliasIndex d L j → ℂ)
    (hfine : ∀ m : CMP89Eq246AliasIndex d L j,
      m ≠ cmp89Eq249CentralAliasIndex d L j →
        cmp89Eq246EntireAliasFineSymbol d L j mass z m ≠ 0)
    (hstabilized :
      cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z ≠ 0)
    (hcolumn : cmp89Eq246EntireAliasAverageColumn d L j z
        (cmp89Eq249CentralAliasIndex d L j) ≠ 0) :
    (cmp89Eq246EntireAliasPrecisionMatrix d L j mass a z).transpose.mulVec
        (cmp89Eq246StabilizedAliasTransposeFullSolution
          d L j mass a z source) =
      source := by
  classical
  let central := cmp89Eq249CentralAliasIndex d L j
  let fine := cmp89Eq246EntireAliasFineSymbol d L j mass z
  let column := cmp89Eq246EntireAliasAverageColumn d L j z
  let row := cmp89Eq246EntireAliasAverageRow d L j z
  let centralPair := cmp89Eq249CentralEntireAveragePair d L j z
  let noncentral := cmp89Eq249ComplexNoncentralAliasSum d L j mass z
  let stabilized :=
    cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z
  let moment :=
    cmp89Eq246StabilizedAliasTransposeFullSolutionMoment
      d L j mass a z source
  let base :=
    cmp89Eq246StabilizedAliasTransposeNoncentralSourceMoment
      d L j mass z source
  let solution :=
    cmp89Eq246StabilizedAliasTransposeFullSolution d L j mass a z source
  have hsum : (∑ n, column n * solution n) = moment := by
    simpa only [column, solution, moment] using
      sum_column_mul_cmp89Eq246StabilizedAliasTransposeFullSolution_eq
        d L j mass a z source hcolumn
  have hpairDirect : column central * row central = centralPair := by
    change cmp89Eq245EntireAverageAmplitude d (L ^ j)
          (cmp89Eq248EntireAliasMomentum z (cmp89Eq249ZeroAlias d)) *
        cmp89Eq245EntireAverageAmplitude d (L ^ j)
          (-cmp89Eq248EntireAliasMomentum z (cmp89Eq249ZeroAlias d)) =
      cmp89Eq245EntireAverageAmplitude d (L ^ j) z *
        cmp89Eq245EntireAverageAmplitude d (L ^ j) (-z)
    have hz :
        cmp89Eq248EntireAliasMomentum z (cmp89Eq249ZeroAlias d) = z := by
      funext mu
      simp [cmp89Eq248EntireAliasMomentum, cmp89Eq249ZeroAlias,
        cmp89Eq245AliasShift]
    rw [hz]
  have hpair : row central * column central = centralPair := by
    rw [mul_comm]
    exact hpairDirect
  have hcentralFine :
      fine central = cmp89Eq249CentralEntireFineSymbol d L j mass z := by
    simp [fine, central, cmp89Eq246EntireAliasFineSymbol,
      cmp89Eq249CentralEntireFineSymbol,
      cmp89Eq248EntireAliasMomentum_zero]
  have hnoncentral :
      (∑ n ∈ Finset.univ.erase central,
        column n * row n / fine n) = noncentral := by
    exact cmp89Eq249AliasSubtypeNoncentralSum_eq d L j mass z
  have hstabilizedEq :
      stabilized = fine central + (a : ℂ) * centralPair +
        (a : ℂ) * fine central * noncentral := by
    dsimp only [stabilized, centralPair, noncentral]
    rw [cmp89Eq249CentralStabilizedAliasDenominator, hcentralFine]
  have hmomentEq :
      moment * stabilized = column central * source central +
        fine central * base := by
    change
      ((column central * source central + fine central * base) / stabilized) *
          stabilized = _
    exact div_mul_cancel₀ _ hstabilized
  have hnoncentralExplicitSum :
      (∑ n ∈ Finset.univ.erase central,
        column n * (source n / fine n -
          (a : ℂ) * row n * moment / fine n)) =
        base - (a : ℂ) * moment * noncentral := by
    have hsource :
        (∑ n ∈ Finset.univ.erase central,
          column n * (source n / fine n)) = base := by
      dsimp only [base,
        cmp89Eq246StabilizedAliasTransposeNoncentralSourceMoment]
      apply Finset.sum_congr rfl
      intro n _
      ring
    have hcorrection :
        (∑ n ∈ Finset.univ.erase central,
          column n * ((a : ℂ) * row n * moment / fine n)) =
          (a : ℂ) * moment *
            (∑ n ∈ Finset.univ.erase central,
              column n * row n / fine n) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    calc
      (∑ n ∈ Finset.univ.erase central,
          column n * (source n / fine n -
            (a : ℂ) * row n * moment / fine n)) =
        (∑ n ∈ Finset.univ.erase central,
          column n * (source n / fine n)) -
          ∑ n ∈ Finset.univ.erase central,
            column n * ((a : ℂ) * row n * moment / fine n) := by
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib]
      _ = base - (a : ℂ) * moment *
          (∑ n ∈ Finset.univ.erase central,
            column n * row n / fine n) := by rw [hsource, hcorrection]
      _ = base - (a : ℂ) * moment * noncentral := by rw [hnoncentral]
  funext m
  rw [cmp89Eq246EntireAliasPrecisionMatrix_transpose_mulVec, hsum]
  change fine m * solution m + (a : ℂ) * row m * moment = source m
  by_cases hm : m = central
  · subst m
    have hcentralSolution :
        solution central =
          (moment - (base - (a : ℂ) * moment * noncentral)) /
            column central := by
      change cmp89Eq246StabilizedAliasTransposeFullSolution
          d L j mass a z source central = _
      simp only [cmp89Eq246StabilizedAliasTransposeFullSolution, central,
        fine, column, row, moment, if_pos]
      rw [hnoncentralExplicitSum]
    rw [hcentralSolution]
    have hdiv :
        fine central *
              (moment - (base - (a : ℂ) * moment * noncentral)) /
            column central =
          source central - (a : ℂ) * row central * moment := by
      apply (div_eq_iff hcolumn).2
      have hmom := hmomentEq
      rw [hstabilizedEq, ← hpair] at hmom
      linear_combination hmom
    have hadded := eq_sub_iff_add_eq.mp hdiv
    convert hadded using 1 <;> ring
  · have hsolution :
        solution m = source m / fine m -
          (a : ℂ) * row m * moment / fine m := by
      simp [solution, cmp89Eq246StabilizedAliasTransposeFullSolution,
        central, fine, column, row, moment, hm]
    rw [hsolution]
    have hfm : fine m ≠ 0 := hfine m hm
    field_simp [hfm]
    ring

end

end YangMills.RG
