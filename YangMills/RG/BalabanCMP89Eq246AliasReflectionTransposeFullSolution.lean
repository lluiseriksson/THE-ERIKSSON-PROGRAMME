/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceAliasReflectionStabilizedSolution
import YangMills.RG.BalabanCMP89Eq246StabilizedAliasTransposeFullSolution

/-!
# Reflection of the arbitrary-source transposed CMP89 (2.46) solve

This is the missing orientation gate between the continuous full-point-source
kernel and the finite physical DFT.  It transports the arbitrary source by
the actual half-open alias reflection, proves equality of the two scalar
moments, and only then identifies the complete transposed solution at `-z`
with the non-transposed solution at `z`.

No self-adjointness, block-norm symmetry, periodization, regional estimate,
window-15 attainment, terminal field, or `TermSource` inhabitant is assumed
or asserted.
-/

namespace YangMills.RG

noncomputable section

/-- Pull an arbitrary source through the actual centered-alias reflection. -/
def cmp89Eq246AliasReflectionSource
    (d M : ℕ) [NeZero M]
    (source : CMP89Eq246AliasIndex d M 1 → ℂ) :
    CMP89Eq246AliasIndex d M 1 → ℂ :=
  fun n => source ((cmp99SourceAliasIndexOneReflection d M).symm n)

@[simp]
theorem cmp89Eq246AliasReflectionSource_apply_reflection
    (d M : ℕ) [NeZero M]
    (source : CMP89Eq246AliasIndex d M 1 → ℂ)
    (m : CMP89Eq246AliasIndex d M 1) :
    cmp89Eq246AliasReflectionSource d M source
        (cmp99SourceAliasIndexOneReflection d M m) = source m := by
  simp [cmp89Eq246AliasReflectionSource]

/-- Reflection exchanges the noncentral column source moment at `-z` with
the noncentral row source moment at `z`. -/
theorem cmp89Eq246StabilizedAliasTransposeNoncentralSourceMoment_neg_reflection
    (d M : ℕ) [NeZero M] (mass : ℝ) (z : Fin d → ℂ)
    (source : CMP89Eq246AliasIndex d M 1 → ℂ) :
    cmp89Eq246StabilizedAliasTransposeNoncentralSourceMoment
        d M 1 mass (-z) (cmp89Eq246AliasReflectionSource d M source) =
      cmp89Eq246StabilizedAliasNoncentralSourceMoment
        d M 1 mass z source := by
  classical
  let central := cmp89Eq249CentralAliasIndex d M 1
  let reflect := cmp99SourceAliasIndexOneReflection d M
  let sourceR := cmp89Eq246AliasReflectionSource d M source
  let transposeTerm := fun n : CMP89Eq246AliasIndex d M 1 =>
    cmp89Eq246EntireAliasAverageColumn d M 1 (-z) n * sourceR n /
      cmp89Eq246EntireAliasFineSymbol d M 1 mass (-z) n
  let directTerm := fun n : CMP89Eq246AliasIndex d M 1 =>
    cmp89Eq246EntireAliasAverageRow d M 1 z n * source n /
      cmp89Eq246EntireAliasFineSymbol d M 1 mass z n
  have hreflectCentral : reflect central = central := by
    exact cmp99SourceAliasIndexOneReflection_central d M
  have hterm : ∀ n, transposeTerm (reflect n) = directTerm n := by
    intro n
    simp only [transposeTerm, directTerm, sourceR]
    rw [cmp89Eq246EntireAliasAverageColumn_neg_reflection_eq_row,
      cmp89Eq246EntireAliasFineSymbol_neg_reflection_eq]
    simp [reflect, sourceR, cmp89Eq246AliasReflectionSource]
  have hfull : (∑ n, transposeTerm n) = ∑ n, directTerm n := by
    calc
      (∑ n, transposeTerm n) = ∑ n, transposeTerm (reflect n) :=
        (Equiv.sum_comp reflect transposeTerm).symm
      _ = ∑ n, directTerm n := by
        apply Finset.sum_congr rfl
        intro n _
        exact hterm n
  have hcentral : transposeTerm central = directTerm central := by
    have h := hterm central
    simpa only [hreflectCentral] using h
  have hleft := Finset.sum_erase_add Finset.univ transposeTerm
    (Finset.mem_univ central)
  have hright := Finset.sum_erase_add Finset.univ directTerm
    (Finset.mem_univ central)
  unfold cmp89Eq246StabilizedAliasTransposeNoncentralSourceMoment
    cmp89Eq246StabilizedAliasNoncentralSourceMoment
  change (∑ n ∈ Finset.univ.erase central, transposeTerm n) =
    ∑ n ∈ Finset.univ.erase central, directTerm n
  calc
    (∑ n ∈ Finset.univ.erase central, transposeTerm n) =
        (∑ n, transposeTerm n) - transposeTerm central := by
      rw [← hleft]
      ring
    _ = (∑ n, directTerm n) - directTerm central := by
      rw [hfull, hcentral]
    _ = ∑ n ∈ Finset.univ.erase central, directTerm n := by
      rw [← hright]
      ring

/-- The complete scalar moments of the reflected transposed and direct
solutions agree. -/
theorem cmp89Eq246StabilizedAliasTransposeFullSolutionMoment_neg_reflection
    (d M : ℕ) [NeZero M] (mass a : ℝ) (z : Fin d → ℂ)
    (source : CMP89Eq246AliasIndex d M 1 → ℂ) :
    cmp89Eq246StabilizedAliasTransposeFullSolutionMoment
        d M 1 mass a (-z) (cmp89Eq246AliasReflectionSource d M source) =
      cmp89Eq246StabilizedAliasFullSolutionMoment
        d M 1 mass a z source := by
  let central := cmp89Eq249CentralAliasIndex d M 1
  let reflect := cmp99SourceAliasIndexOneReflection d M
  have hreflectCentral : reflect central = central :=
    cmp99SourceAliasIndexOneReflection_central d M
  have hcolumn :=
    cmp89Eq246EntireAliasAverageColumn_neg_reflection_eq_row
      (d := d) (M := M) z central
  rw [hreflectCentral] at hcolumn
  have hfine :=
    cmp89Eq246EntireAliasFineSymbol_neg_reflection_eq
      (d := d) (M := M) mass z central
  rw [hreflectCentral] at hfine
  have hreflectCentralSymm :
      (cmp99SourceAliasIndexOneReflection d M).symm
          (cmp89Eq249CentralAliasIndex d M 1) =
        cmp89Eq249CentralAliasIndex d M 1 := by
    apply (cmp99SourceAliasIndexOneReflection d M).injective
    simp [cmp99SourceAliasIndexOneReflection_central]
  rw [cmp89Eq246StabilizedAliasTransposeFullSolutionMoment,
    cmp89Eq246StabilizedAliasFullSolutionMoment,
    cmp89Eq246StabilizedAliasTransposeNoncentralSourceMoment_neg_reflection,
    cmp89Eq249CentralStabilizedAliasDenominator_neg,
    hcolumn, hfine]
  simp [central, cmp89Eq246AliasReflectionSource, hreflectCentralSymm]

/-- The arbitrary-source transposed solution at opposite momentum is the
direct solution with both its source and output alias transported by the
actual half-open reflection.  This is the orientation bridge needed before
finite-grid periodization; it is not an appeal to abstract self-adjointness. -/
theorem cmp89Eq246StabilizedAliasTransposeFullSolution_neg_reflection
    (d M : ℕ) [NeZero M] (mass a : ℝ) (z : Fin d → ℂ)
    (source : CMP89Eq246AliasIndex d M 1 → ℂ)
    (m : CMP89Eq246AliasIndex d M 1) :
    cmp89Eq246StabilizedAliasTransposeFullSolution
        d M 1 mass a (-z) (cmp89Eq246AliasReflectionSource d M source)
        (cmp99SourceAliasIndexOneReflection d M m) =
      cmp89Eq246StabilizedAliasFullSolution d M 1 mass a z source m := by
  classical
  let central := cmp89Eq249CentralAliasIndex d M 1
  let reflect := cmp99SourceAliasIndexOneReflection d M
  let sourceR := cmp89Eq246AliasReflectionSource d M source
  let momentT :=
    cmp89Eq246StabilizedAliasTransposeFullSolutionMoment
      d M 1 mass a (-z) sourceR
  let moment :=
    cmp89Eq246StabilizedAliasFullSolutionMoment d M 1 mass a z source
  let transposeCorrection := fun n : CMP89Eq246AliasIndex d M 1 =>
    cmp89Eq246EntireAliasAverageColumn d M 1 (-z) n *
      (sourceR n / cmp89Eq246EntireAliasFineSymbol d M 1 mass (-z) n -
        (a : ℂ) * cmp89Eq246EntireAliasAverageRow d M 1 (-z) n * momentT /
          cmp89Eq246EntireAliasFineSymbol d M 1 mass (-z) n)
  let directCorrection := fun n : CMP89Eq246AliasIndex d M 1 =>
    cmp89Eq246EntireAliasAverageRow d M 1 z n *
      (source n / cmp89Eq246EntireAliasFineSymbol d M 1 mass z n -
        (a : ℂ) * cmp89Eq246EntireAliasAverageColumn d M 1 z n * moment /
          cmp89Eq246EntireAliasFineSymbol d M 1 mass z n)
  have hreflectCentral : reflect central = central :=
    cmp99SourceAliasIndexOneReflection_central d M
  have hmoment : momentT = moment := by
    exact cmp89Eq246StabilizedAliasTransposeFullSolutionMoment_neg_reflection
      d M mass a z source
  have hcorrection :
      (∑ n ∈ Finset.univ.erase central, transposeCorrection n) =
        ∑ n ∈ Finset.univ.erase central, directCorrection n := by
    let fullT := ∑ n, transposeCorrection n
    let fullD := ∑ n, directCorrection n
    have hterm : ∀ n, transposeCorrection (reflect n) = directCorrection n := by
      intro n
      simp only [transposeCorrection, directCorrection, sourceR]
      rw [cmp89Eq246EntireAliasAverageColumn_neg_reflection_eq_row,
        cmp89Eq246EntireAliasAverageRow_neg_reflection_eq_column,
        cmp89Eq246EntireAliasFineSymbol_neg_reflection_eq, hmoment]
      simp [reflect, cmp89Eq246AliasReflectionSource]
    have hfull : fullT = fullD := by
      calc
        fullT = ∑ n, transposeCorrection (reflect n) := by
          exact (Equiv.sum_comp reflect transposeCorrection).symm
        _ = fullD := by
          apply Finset.sum_congr rfl
          intro n _
          exact hterm n
    have hcentral : transposeCorrection central = directCorrection central := by
      have h := hterm central
      simpa only [hreflectCentral] using h
    have hleft := Finset.sum_erase_add Finset.univ transposeCorrection
      (Finset.mem_univ central)
    have hright := Finset.sum_erase_add Finset.univ directCorrection
      (Finset.mem_univ central)
    calc
      (∑ n ∈ Finset.univ.erase central, transposeCorrection n) =
          fullT - transposeCorrection central := by
        dsimp only [fullT]
        rw [← hleft]
        ring
      _ = fullD - directCorrection central := by rw [hfull, hcentral]
      _ = ∑ n ∈ Finset.univ.erase central, directCorrection n := by
        dsimp only [fullD]
        rw [← hright]
        ring
  by_cases hm : m = central
  · subst m
    rw [show reflect central = central by exact hreflectCentral]
    simp only [cmp89Eq246StabilizedAliasTransposeFullSolution,
      cmp89Eq246StabilizedAliasFullSolution, central, if_pos]
    change
      (momentT - ∑ n ∈ Finset.univ.erase central, transposeCorrection n) /
          cmp89Eq246EntireAliasAverageColumn d M 1 (-z) central =
        (moment - ∑ n ∈ Finset.univ.erase central, directCorrection n) /
          cmp89Eq246EntireAliasAverageRow d M 1 z central
    have hcolumn :=
      cmp89Eq246EntireAliasAverageColumn_neg_reflection_eq_row
        (d := d) (M := M) z central
    rw [hreflectCentral] at hcolumn
    rw [hmoment, hcorrection, hcolumn]
  · have hreflectNe : reflect m ≠ central := by
      intro h
      apply hm
      apply reflect.injective
      rw [h]
      exact hreflectCentral.symm
    have hreflectNe' :
        cmp99SourceAliasIndexOneReflection d M m ≠
          cmp89Eq249CentralAliasIndex d M 1 := by
      simpa only [reflect, central] using hreflectNe
    have hm' : m ≠ cmp89Eq249CentralAliasIndex d M 1 := by
      simpa only [central] using hm
    have hmoment' :
        cmp89Eq246StabilizedAliasTransposeFullSolutionMoment
            d M 1 mass a (-z) (cmp89Eq246AliasReflectionSource d M source) =
          cmp89Eq246StabilizedAliasFullSolutionMoment d M 1 mass a z source := by
      simpa only [momentT, moment, sourceR] using hmoment
    simp only [cmp89Eq246StabilizedAliasTransposeFullSolution,
      cmp89Eq246StabilizedAliasFullSolution, hreflectNe', hm', if_false]
    rw [cmp89Eq246EntireAliasFineSymbol_neg_reflection_eq,
      cmp89Eq246EntireAliasAverageRow_neg_reflection_eq_column, hmoment']
    simp [reflect, sourceR, cmp89Eq246AliasReflectionSource]

end

end YangMills.RG
