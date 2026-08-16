/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq249StabilizedAliasTransposeSolution
import YangMills.RG.BalabanCMP89Eq248FineLatticeFourierGreenLeftDerivative

/-!
# Central-stabilized column solution and endpoint sum

PRE-VALIDATION: this source is present, its `.olean` has not yet been
materialized, and its declarations have not yet been compiler verified.

The physical Green endpoint in CMP89 carries the direct-momentum averaging
column.  The already sealed weighted-adjoint synthesis instead carries the
opposite-momentum row and therefore the transposed solution.  This file builds
the missing column-oriented object directly: it uses the same removable
central cancellation, proves that the resulting vector solves the original
alias matrix, and identifies its complete phase-weighted alias sum with the
literal stabilized Green endpoint integrand.

This is an analytic normal form only.  It does not identify the physical row
sum with this column sum, reindex through Fourier negation or the affine alias
carry, periodize the Green kernel, construct regional `B0`, attain window 15,
discharge a terminal field, or inhabit `TermSource`.
-/

namespace YangMills.RG

open Matrix

noncomputable section

/-- The central-stabilized solution of the original alias matrix in the
direct-momentum column orientation. -/
def cmp89Eq249StabilizedAliasColumnSolution
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin d → ℂ) :
    CMP89Eq246AliasIndex d L j → ℂ :=
  fun m =>
    if m = cmp89Eq249CentralAliasIndex d L j then
      cmp89Eq246EntireAliasAverageColumn d L j z m /
        cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z
    else
      cmp89Eq249CentralEntireFineSymbol d L j mass z *
          cmp89Eq246EntireAliasAverageColumn d L j z m /
        (cmp89Eq246EntireAliasFineSymbol d L j mass z m *
          cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z)

@[simp]
theorem cmp89Eq249StabilizedAliasColumnSolution_central
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin d → ℂ) :
    cmp89Eq249StabilizedAliasColumnSolution d L j mass a z
        (cmp89Eq249CentralAliasIndex d L j) =
      cmp89Eq246EntireAliasAverageColumn d L j z
          (cmp89Eq249CentralAliasIndex d L j) /
        cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z := by
  simp [cmp89Eq249StabilizedAliasColumnSolution]

theorem cmp89Eq249StabilizedAliasColumnSolution_noncentral
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin d → ℂ)
    (m : CMP89Eq246AliasIndex d L j)
    (hm : m ≠ cmp89Eq249CentralAliasIndex d L j) :
    cmp89Eq249StabilizedAliasColumnSolution d L j mass a z m =
      cmp89Eq249CentralEntireFineSymbol d L j mass z *
          cmp89Eq246EntireAliasAverageColumn d L j z m /
        (cmp89Eq246EntireAliasFineSymbol d L j mass z m *
          cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z) := by
  simp [cmp89Eq249StabilizedAliasColumnSolution, hm]

/-- The internally defined column vector solves the original entire alias
matrix.  The removable central fine-symbol zero is never inverted. -/
theorem cmp89Eq246EntireAliasPrecisionMatrix_mulVec_stabilizedColumnSolution
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin d → ℂ)
    (hfine : ∀ m : CMP89Eq246AliasIndex d L j,
      m ≠ cmp89Eq249CentralAliasIndex d L j →
        cmp89Eq246EntireAliasFineSymbol d L j mass z m ≠ 0)
    (hstabilized :
      cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z ≠ 0) :
    (cmp89Eq246EntireAliasPrecisionMatrix d L j mass a z).mulVec
        (cmp89Eq249StabilizedAliasColumnSolution d L j mass a z) =
      cmp89Eq246EntireAliasAverageColumn d L j z := by
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
  let solution := cmp89Eq249StabilizedAliasColumnSolution d L j mass a z
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
      stabilized =
        centralFine + (a : ℂ) * centralPair +
          (a : ℂ) * centralFine * noncentral := rfl
  have hstabilized' : stabilized ≠ 0 := by
    simpa only [stabilized] using hstabilized
  have hnoncentralSolution :
      (∑ n ∈ Finset.univ.erase central, row n * solution n) =
        centralFine * noncentral / stabilized := by
    calc
      (∑ n ∈ Finset.univ.erase central, row n * solution n) =
          ∑ n ∈ Finset.univ.erase central,
            centralFine * (row n * column n / fine n) / stabilized := by
        apply Finset.sum_congr rfl
        intro n hn
        have hncentral : n ≠ central := (Finset.mem_erase.mp hn).1
        have hsolutionN :
            solution n = centralFine * column n / (fine n * stabilized) := by
          simpa only [solution, centralFine, column, fine, stabilized, central]
            using cmp89Eq249StabilizedAliasColumnSolution_noncentral
              d L j mass a z n hncentral
        rw [hsolutionN]
        have hfn : fine n ≠ 0 := hfine n hncentral
        change row n *
            (centralFine * column n / (fine n * stabilized)) = _
        field_simp [hfn, hstabilized']
      _ = centralFine *
          (∑ n ∈ Finset.univ.erase central,
            row n * column n / fine n) / stabilized := by
        rw [← Finset.sum_div, ← Finset.mul_sum]
      _ = centralFine * noncentral / stabilized := by
        rw [hnoncentral]
  have hsumSolution :
      (∑ n, row n * solution n) =
        (centralPair + centralFine * noncentral) / stabilized := by
    rw [← Finset.sum_erase_add Finset.univ
      (fun n => row n * solution n) (Finset.mem_univ central)]
    rw [hnoncentralSolution]
    have hcentralSolution :
        solution central = column central / stabilized := by
      simpa only [solution, column, stabilized, central] using
        cmp89Eq249StabilizedAliasColumnSolution_central
          d L j mass a z
    rw [hcentralSolution]
    field_simp [hstabilized']
    have hcentralPair' : row central * column central = centralPair := by
      simpa only [mul_comm] using hcentralPair
    rw [hcentralPair']
    ring
  funext m
  rw [cmp89Eq246EntireAliasPrecisionMatrix_mulVec, hsumSolution]
  change fine m * solution m +
      (a : ℂ) * column m *
        ((centralPair + centralFine * noncentral) / stabilized) = column m
  by_cases hm : m = central
  · subst m
    have hcentralSolution :
        solution central = column central / stabilized := by
      simpa only [solution, column, stabilized, central] using
        cmp89Eq249StabilizedAliasColumnSolution_central
          d L j mass a z
    rw [hcentralSolution, hcentralFine]
    field_simp [hstabilized']
    rw [hstabilizedEq]
    ring
  · have hsolution :
        solution m = centralFine * column m / (fine m * stabilized) := by
      simpa only [solution, centralFine, column, fine, stabilized, central]
        using cmp89Eq249StabilizedAliasColumnSolution_noncentral
          d L j mass a z m hm
    have hfm : fine m ≠ 0 := hfine m hm
    rw [hsolution]
    field_simp [hfm, hstabilized']
    rw [hstabilizedEq]
    ring

/-- The noncentral subtype sum of bare endpoint numerators is the literal
noncentral raw-alias sum used in the stabilized endpoint numerator. -/
theorem cmp89Eq249AliasSubtypeNoncentralGreenEndpointSum_eq
    (d L j : ℕ) [NeZero L] (mass : ℝ) (z : Fin d → ℂ)
    (endpointDisplacement : Fin d → ℝ) :
    (∑ n ∈ Finset.univ.erase (cmp89Eq249CentralAliasIndex d L j),
        cmp89Eq248ComplexBareGreenEndpointNumerator d L j z n.1
            endpointDisplacement /
          cmp89Eq246EntireAliasFineSymbol d L j mass z n) =
      ∑ m ∈ (cmp89Eq245CenteredAliasVectors d (L ^ j)).erase
          (cmp89Eq249ZeroAlias d),
        cmp89Eq248ComplexBareGreenEndpointNumerator d L j z m
            endpointDisplacement /
          cmp89Eq245EntireScaledLaplacianSymbol
            d (((L : ℝ) ^ j)⁻¹) mass
              (cmp89Eq248EntireAliasMomentum z m) := by
  classical
  let aliases := cmp89Eq245CenteredAliasVectors d (L ^ j)
  let zeroAlias := cmp89Eq249ZeroAlias d
  let central := cmp89Eq249CentralAliasIndex d L j
  let subtypeTerm := fun n : CMP89Eq246AliasIndex d L j =>
    cmp89Eq248ComplexBareGreenEndpointNumerator d L j z n.1
        endpointDisplacement /
      cmp89Eq246EntireAliasFineSymbol d L j mass z n
  let printedTerm := fun m : Fin d → ℤ =>
    cmp89Eq248ComplexBareGreenEndpointNumerator d L j z m
        endpointDisplacement /
      cmp89Eq245EntireScaledLaplacianSymbol
        d (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z m)
  have hzero : zeroAlias ∈ aliases := cmp89Eq249ZeroAlias_mem d L j
  have hfull :
      (∑ n : CMP89Eq246AliasIndex d L j, subtypeTerm n) =
        ∑ m ∈ aliases, printedTerm m := by
    rw [Finset.sum_subtype aliases (fun _ => Iff.rfl)]
    apply Finset.sum_congr rfl
    intro m _
    rfl
  have hcentral : subtypeTerm central = printedTerm zeroAlias := by
    rfl
  have hleft := Finset.sum_erase_add Finset.univ subtypeTerm
    (Finset.mem_univ central)
  have hright := Finset.sum_erase_add aliases printedTerm hzero
  change (∑ n ∈ Finset.univ.erase central, subtypeTerm n) =
    ∑ m ∈ aliases.erase zeroAlias, printedTerm m
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

/-- The complete phase-weighted column solution is exactly the literal
stabilized Green endpoint integrand.  No integral or volume normalization is
inserted. -/
theorem sum_exp_mul_cmp89Eq249StabilizedAliasColumnSolution_eq_endpointIntegrand
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin d → ℂ)
    (endpointDisplacement : Fin d → ℝ) :
    (∑ n : CMP89Eq246AliasIndex d L j,
        Complex.exp (Complex.I * cmp89Eq251EntirePhase
            (cmp89Eq248EntireAliasMomentum z n.1) endpointDisplacement) *
          cmp89Eq249StabilizedAliasColumnSolution d L j mass a z n) =
      cmp89Eq248ComplexStabilizedGreenEndpointIntegrand
        d L j mass a z endpointDisplacement := by
  classical
  let central := cmp89Eq249CentralAliasIndex d L j
  let zeroAlias := cmp89Eq249ZeroAlias d
  let centralFine := cmp89Eq249CentralEntireFineSymbol d L j mass z
  let stabilized :=
    cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z
  let solution := cmp89Eq249StabilizedAliasColumnSolution d L j mass a z
  let phase := fun n : CMP89Eq246AliasIndex d L j =>
    Complex.exp (Complex.I * cmp89Eq251EntirePhase
      (cmp89Eq248EntireAliasMomentum z n.1) endpointDisplacement)
  let bare := fun m : Fin d → ℤ =>
    cmp89Eq248ComplexBareGreenEndpointNumerator
      d L j z m endpointDisplacement
  let fine := cmp89Eq246EntireAliasFineSymbol d L j mass z
  have hcentral :
      phase central * solution central = bare zeroAlias / stabilized := by
    have hsolution :
        solution central =
          cmp89Eq246EntireAliasAverageColumn d L j z central /
            stabilized := by
      simpa only [solution, stabilized, central] using
        cmp89Eq249StabilizedAliasColumnSolution_central
          d L j mass a z
    rw [hsolution]
    change
      Complex.exp (Complex.I * cmp89Eq251EntirePhase
          (cmp89Eq248EntireAliasMomentum z zeroAlias)
            endpointDisplacement) *
          (cmp89Eq245EntireAverageAmplitude d (L ^ j)
            (cmp89Eq248EntireAliasMomentum z zeroAlias) / stabilized) =
        (Complex.exp (Complex.I * cmp89Eq251EntirePhase
            (cmp89Eq248EntireAliasMomentum z zeroAlias)
              endpointDisplacement) *
          cmp89Eq245EntireAverageAmplitude d (L ^ j)
            (cmp89Eq248EntireAliasMomentum z zeroAlias)) / stabilized
    ring
  have hnoncentral :
      (∑ n ∈ Finset.univ.erase central, phase n * solution n) =
        centralFine *
          (∑ n ∈ Finset.univ.erase central, bare n.1 / fine n) /
            stabilized := by
    calc
      (∑ n ∈ Finset.univ.erase central, phase n * solution n) =
          ∑ n ∈ Finset.univ.erase central,
            centralFine * (bare n.1 / fine n) / stabilized := by
        apply Finset.sum_congr rfl
        intro n hn
        have hncentral : n ≠ central := (Finset.mem_erase.mp hn).1
        have hsolution :
            solution n = centralFine *
                cmp89Eq246EntireAliasAverageColumn d L j z n /
              (fine n * stabilized) := by
          simpa only [solution, centralFine, fine, stabilized, central] using
            cmp89Eq249StabilizedAliasColumnSolution_noncentral
              d L j mass a z n hncentral
        rw [hsolution]
        change
          Complex.exp (Complex.I * cmp89Eq251EntirePhase
              (cmp89Eq248EntireAliasMomentum z n.1)
                endpointDisplacement) *
              (centralFine *
                cmp89Eq245EntireAverageAmplitude d (L ^ j)
                  (cmp89Eq248EntireAliasMomentum z n.1) /
                (fine n * stabilized)) =
            centralFine *
              ((Complex.exp (Complex.I * cmp89Eq251EntirePhase
                  (cmp89Eq248EntireAliasMomentum z n.1)
                    endpointDisplacement) *
                cmp89Eq245EntireAverageAmplitude d (L ^ j)
                  (cmp89Eq248EntireAliasMomentum z n.1)) / fine n) /
              stabilized
        ring
      _ = centralFine *
          (∑ n ∈ Finset.univ.erase central, bare n.1 / fine n) /
            stabilized := by
        rw [← Finset.sum_div, ← Finset.mul_sum]
  have hraw := cmp89Eq249AliasSubtypeNoncentralGreenEndpointSum_eq
    d L j mass z endpointDisplacement
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun n => phase n * solution n) (Finset.mem_univ central)
  calc
    (∑ n : CMP89Eq246AliasIndex d L j, phase n * solution n) =
        phase central * solution central +
          ∑ n ∈ Finset.univ.erase central, phase n * solution n := by
      rw [← hsplit]
      ring
    _ = bare zeroAlias / stabilized +
        centralFine *
          (∑ m ∈ (cmp89Eq245CenteredAliasVectors d (L ^ j)).erase
              zeroAlias,
            bare m /
              cmp89Eq245EntireScaledLaplacianSymbol
                d (((L : ℝ) ^ j)⁻¹) mass
                  (cmp89Eq248EntireAliasMomentum z m)) /
          stabilized := by
      rw [hcentral, hnoncentral, hraw]
    _ = cmp89Eq248ComplexStabilizedGreenEndpointIntegrand
        d L j mass a z endpointDisplacement := by
      unfold cmp89Eq248ComplexStabilizedGreenEndpointIntegrand
        cmp89Eq248ComplexStabilizedGreenEndpointNumerator
      change bare zeroAlias / stabilized +
          centralFine *
            (∑ m ∈ (cmp89Eq245CenteredAliasVectors d (L ^ j)).erase
                zeroAlias,
              bare m /
                cmp89Eq245EntireScaledLaplacianSymbol
                  d (((L : ℝ) ^ j)⁻¹) mass
                    (cmp89Eq248EntireAliasMomentum z m)) /
            stabilized =
        (bare zeroAlias + centralFine *
          ∑ m ∈ (cmp89Eq245CenteredAliasVectors d (L ^ j)).erase
              zeroAlias,
            bare m /
              cmp89Eq245EntireScaledLaplacianSymbol
                d (((L : ℝ) ^ j)⁻¹) mass
                  (cmp89Eq248EntireAliasMomentum z m)) / stabilized
      ring

end

end YangMills.RG
