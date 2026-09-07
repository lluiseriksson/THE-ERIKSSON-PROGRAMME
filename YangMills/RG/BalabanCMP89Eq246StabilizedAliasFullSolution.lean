/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq249StabilizedAliasColumnSolution

/-!
# Stabilized full alias-fibre solution for CMP89 (2.46)

CMP89 (2.46) solves the finite alias system for an arbitrary fine-lattice
source before the specialization `f = Q_j^* g` that leads to (2.48).  This
module keeps that source role visible.  It constructs the solution of the
literal diagonal-plus-rank-one matrix internally, with the central pole
cancelled before division.

The distinguished central component is recovered from the exact row moment,
so the construction never divides by the central fine symbol.  It assumes
nonvanishing only of the noncentral fine symbols, the stabilized denominator,
and the central opposite-momentum average.  It does not yet perform the
Fourier synthesis, produce the full fine-to-fine Green kernel, reflect that
kernel at a Dirichlet boundary, or attain window 15.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.

Cold compiler evidence for exact source checkpoint
`febce96d017f4ec8494354656f88b0dca56c1854` is recorded in Verification
Ledger Addendum 1008. The focal and its exact two-declaration axiom audit
passed in GitHub Actions run `33470345841` without restoring a project graph.
-/

namespace YangMills.RG

open Matrix

noncomputable section

/-- The noncentral row moment of an arbitrary fine source. -/
def cmp89Eq246StabilizedAliasNoncentralSourceMoment
    (d L j : ℕ) [NeZero L] (mass : ℝ) (z : Fin d → ℂ)
    (source : CMP89Eq246AliasIndex d L j → ℂ) : ℂ :=
  ∑ n ∈ Finset.univ.erase (cmp89Eq249CentralAliasIndex d L j),
    cmp89Eq246EntireAliasAverageRow d L j z n * source n /
      cmp89Eq246EntireAliasFineSymbol d L j mass z n

/-- The exact row moment of the stabilized solution. -/
def cmp89Eq246StabilizedAliasFullSolutionMoment
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin d → ℂ)
    (source : CMP89Eq246AliasIndex d L j → ℂ) : ℂ :=
  let central := cmp89Eq249CentralAliasIndex d L j
  let fine := cmp89Eq246EntireAliasFineSymbol d L j mass z
  let row := cmp89Eq246EntireAliasAverageRow d L j z
  (row central * source central +
      fine central *
        cmp89Eq246StabilizedAliasNoncentralSourceMoment
          d L j mass z source) /
    cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z

/-- The source-faithful solution of the complete alias system in (2.46).

The central branch is defined from the total row moment.  Every noncentral
branch is the literal diagonal inverse followed by the rank-one correction. -/
def cmp89Eq246StabilizedAliasFullSolution
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin d → ℂ)
    (source : CMP89Eq246AliasIndex d L j → ℂ) :
    CMP89Eq246AliasIndex d L j → ℂ :=
  let central := cmp89Eq249CentralAliasIndex d L j
  let fine := cmp89Eq246EntireAliasFineSymbol d L j mass z
  let column := cmp89Eq246EntireAliasAverageColumn d L j z
  let row := cmp89Eq246EntireAliasAverageRow d L j z
  let moment :=
    cmp89Eq246StabilizedAliasFullSolutionMoment d L j mass a z source
  fun m =>
    if m = central then
      (moment -
          ∑ n ∈ Finset.univ.erase central,
            row n *
              (source n / fine n -
                (a : ℂ) * column n * moment / fine n)) /
        row central
    else
      source m / fine m - (a : ℂ) * column m * moment / fine m

/-- By construction, the complete row moment of the stabilized solution is
the named scalar moment. -/
theorem sum_row_mul_cmp89Eq246StabilizedAliasFullSolution_eq
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin d → ℂ)
    (source : CMP89Eq246AliasIndex d L j → ℂ)
    (hrow : cmp89Eq246EntireAliasAverageRow d L j z
        (cmp89Eq249CentralAliasIndex d L j) ≠ 0) :
    (∑ n, cmp89Eq246EntireAliasAverageRow d L j z n *
        cmp89Eq246StabilizedAliasFullSolution d L j mass a z source n) =
      cmp89Eq246StabilizedAliasFullSolutionMoment d L j mass a z source := by
  classical
  let central := cmp89Eq249CentralAliasIndex d L j
  let fine := cmp89Eq246EntireAliasFineSymbol d L j mass z
  let column := cmp89Eq246EntireAliasAverageColumn d L j z
  let row := cmp89Eq246EntireAliasAverageRow d L j z
  let moment :=
    cmp89Eq246StabilizedAliasFullSolutionMoment d L j mass a z source
  let noncentralSolution := fun n : CMP89Eq246AliasIndex d L j =>
    source n / fine n - (a : ℂ) * column n * moment / fine n
  rw [← Finset.sum_erase_add Finset.univ
    (fun n => row n *
      cmp89Eq246StabilizedAliasFullSolution d L j mass a z source n)
    (Finset.mem_univ central)]
  have hcentral :
      cmp89Eq246StabilizedAliasFullSolution d L j mass a z source central =
        (moment - ∑ n ∈ Finset.univ.erase central,
          row n * noncentralSolution n) / row central := by
    simp [cmp89Eq246StabilizedAliasFullSolution, central, fine, column,
      row, moment, noncentralSolution]
  rw [hcentral]
  have hnoncentral :
      (∑ n ∈ Finset.univ.erase central,
        row n * cmp89Eq246StabilizedAliasFullSolution
          d L j mass a z source n) =
        ∑ n ∈ Finset.univ.erase central, row n * noncentralSolution n := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnc : n ≠ central := (Finset.mem_erase.mp hn).1
    simp [cmp89Eq246StabilizedAliasFullSolution, central, fine, column,
      row, moment, noncentralSolution, hnc]
  rw [hnoncentral]
  rw [← mul_div_assoc, mul_div_cancel_left₀ _ hrow]
  ring

/-- The internally constructed full solution solves the literal alias matrix
for an arbitrary fine source.  This is the finite-dimensional content of
CMP89 (2.46), before Fourier synthesis and before the `Q_j^*` specialization
of (2.48). -/
theorem cmp89Eq246EntireAliasPrecisionMatrix_mulVec_stabilizedFullSolution
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin d → ℂ)
    (source : CMP89Eq246AliasIndex d L j → ℂ)
    (hfine : ∀ m : CMP89Eq246AliasIndex d L j,
      m ≠ cmp89Eq249CentralAliasIndex d L j →
        cmp89Eq246EntireAliasFineSymbol d L j mass z m ≠ 0)
    (hstabilized :
      cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z ≠ 0)
    (hrow : cmp89Eq246EntireAliasAverageRow d L j z
        (cmp89Eq249CentralAliasIndex d L j) ≠ 0) :
    (cmp89Eq246EntireAliasPrecisionMatrix d L j mass a z).mulVec
        (cmp89Eq246StabilizedAliasFullSolution d L j mass a z source) =
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
    cmp89Eq246StabilizedAliasFullSolutionMoment d L j mass a z source
  let base :=
    cmp89Eq246StabilizedAliasNoncentralSourceMoment d L j mass z source
  let solution :=
    cmp89Eq246StabilizedAliasFullSolution d L j mass a z source
  have hsum : (∑ n, row n * solution n) = moment := by
    simpa only [row, solution, moment] using
      sum_row_mul_cmp89Eq246StabilizedAliasFullSolution_eq
        d L j mass a z source hrow
  have hpair : column central * row central = centralPair := by
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
  have hcentralFine :
      fine central = cmp89Eq249CentralEntireFineSymbol d L j mass z := by
    simp [fine, central, cmp89Eq246EntireAliasFineSymbol,
      cmp89Eq249CentralEntireFineSymbol,
      cmp89Eq248EntireAliasMomentum_zero]
  have hnoncentral :
      (∑ n ∈ Finset.univ.erase central,
        row n * column n / fine n) = noncentral := by
    calc
      (∑ n ∈ Finset.univ.erase central,
          row n * column n / fine n) =
        ∑ n ∈ Finset.univ.erase central,
          column n * row n / fine n := by
            apply Finset.sum_congr rfl
            intro n _
            ring
      _ = noncentral :=
        cmp89Eq249AliasSubtypeNoncentralSum_eq d L j mass z
  have hstabilizedEq :
      stabilized = fine central + (a : ℂ) * centralPair +
        (a : ℂ) * fine central * noncentral := by
    dsimp only [stabilized, centralPair, noncentral]
    rw [cmp89Eq249CentralStabilizedAliasDenominator, hcentralFine]
  have hmomentEq :
      moment * stabilized = row central * source central +
        fine central * base := by
    change
      ((row central * source central + fine central * base) / stabilized) *
          stabilized = _
    exact div_mul_cancel₀ _ hstabilized
  have hnoncentralExplicitSum :
      (∑ n ∈ Finset.univ.erase central,
        row n * (source n / fine n -
          (a : ℂ) * column n * moment / fine n)) =
        base - (a : ℂ) * moment * noncentral := by
    have hsource :
        (∑ n ∈ Finset.univ.erase central,
          row n * (source n / fine n)) = base := by
      dsimp only [base, cmp89Eq246StabilizedAliasNoncentralSourceMoment]
      apply Finset.sum_congr rfl
      intro n _
      ring
    have hcorrection :
        (∑ n ∈ Finset.univ.erase central,
          row n * ((a : ℂ) * column n * moment / fine n)) =
          (a : ℂ) * moment *
            (∑ n ∈ Finset.univ.erase central,
              row n * column n / fine n) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    calc
      (∑ n ∈ Finset.univ.erase central,
          row n * (source n / fine n -
            (a : ℂ) * column n * moment / fine n)) =
        (∑ n ∈ Finset.univ.erase central,
          row n * (source n / fine n)) -
          ∑ n ∈ Finset.univ.erase central,
            row n * ((a : ℂ) * column n * moment / fine n) := by
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib]
      _ = base - (a : ℂ) * moment *
          (∑ n ∈ Finset.univ.erase central,
            row n * column n / fine n) := by rw [hsource, hcorrection]
      _ = base - (a : ℂ) * moment * noncentral := by rw [hnoncentral]
  funext m
  rw [cmp89Eq246EntireAliasPrecisionMatrix_mulVec, hsum]
  change fine m * solution m + (a : ℂ) * column m * moment = source m
  by_cases hm : m = central
  · subst m
    have hcentralSolution :
        solution central =
          (moment - (base - (a : ℂ) * moment * noncentral)) /
            row central := by
      change cmp89Eq246StabilizedAliasFullSolution
          d L j mass a z source central = _
      simp only [cmp89Eq246StabilizedAliasFullSolution, central,
        fine, column, row, moment, if_pos]
      rw [hnoncentralExplicitSum]
    rw [hcentralSolution]
    have hdiv :
        fine central *
              (moment - (base - (a : ℂ) * moment * noncentral)) /
            row central =
          source central - (a : ℂ) * column central * moment := by
      apply (div_eq_iff hrow).2
      have hmom := hmomentEq
      rw [hstabilizedEq, ← hpair] at hmom
      linear_combination hmom
    have hadded := eq_sub_iff_add_eq.mp hdiv
    convert hadded using 1 <;> ring
  · have hsolution :
        solution m = source m / fine m -
          (a : ℂ) * column m * moment / fine m := by
      simp [solution, cmp89Eq246StabilizedAliasFullSolution, central,
        fine, column, row, moment, hm]
    rw [hsolution]
    have hfm : fine m ≠ 0 := hfine m hm
    field_simp [hfm]
    ring

end

end YangMills.RG
