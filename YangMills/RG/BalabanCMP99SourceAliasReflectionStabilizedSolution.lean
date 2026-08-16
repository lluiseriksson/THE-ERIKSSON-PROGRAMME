/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceAliasReflectionCoefficients
import YangMills.RG.BalabanCMP89Eq249StabilizedAliasColumnSolution

/-!
# Alias-reflection transport of the central-stabilized solution

The sealed coefficient reflection exchanges the direct-momentum column and
opposite-momentum row and preserves the fine symbol.  This file performs the
remaining algebra on the complete finite alias fibre: the actual half-open
carrier reflection fixes the central alias, reindexes the noncentral sum,
preserves the stabilized denominator, and transports the transposed solution
at opposite momentum to the column solution at direct momentum.

This is still the simple CMP89 alias reflection, not the complete physical
cross-fibre orientation bridge.  The affine coarse-fibre carry, physical
finite-sum reindexing, Brillouin periodization, regional `B0`, window 15,
terminal fields and `TermSource` remain open.
-/

namespace YangMills.RG

noncomputable section

/-- Residue reflection fixes the central integer of the printed half-open
alias interval. -/
@[simp]
theorem cmp99SourceCenteredAliasReflection_zero
    {M : ℕ} [NeZero M] :
    cmp99SourceCenteredAliasReflection M
        ⟨0, zero_mem_cmp89Eq245CenteredAliasIntegers
          (Nat.pos_of_ne_zero (NeZero.ne M))⟩ =
      ⟨0, zero_mem_cmp89Eq245CenteredAliasIntegers
        (Nat.pos_of_ne_zero (NeZero.ne M))⟩ := by
  let zeroAlias :
      {m : ℤ // m ∈ cmp89Eq245CenteredAliasIntegers M} :=
    ⟨0, zero_mem_cmp89Eq245CenteredAliasIntegers
      (Nat.pos_of_ne_zero (NeZero.ne M))⟩
  change cmp99SourceCenteredAliasReflection M zeroAlias = zeroAlias
  apply (cmp99SourceCenteredAliasResidueEquiv M).injective
  change
    cmp99SourceCenteredAliasResidueEquiv M
        ((cmp99SourceCenteredAliasResidueEquiv M).symm
          (-(cmp99SourceCenteredAliasResidueEquiv M zeroAlias))) =
      cmp99SourceCenteredAliasResidueEquiv M zeroAlias
  rw [Equiv.apply_symm_apply]
  rw [cmp99SourceCenteredAliasResidueEquiv_apply]
  simp [zeroAlias]

/-- The transported depth-one reflection fixes the distinguished zero alias. -/
@[simp]
theorem cmp99SourceAliasIndexOneReflection_central
    (d M : ℕ) [NeZero M] :
    cmp99SourceAliasIndexOneReflection d M
        (cmp89Eq249CentralAliasIndex d M 1) =
      cmp89Eq249CentralAliasIndex d M 1 := by
  apply (cmp99SourceFlatQprimeAliasIndexOneVectorEquiv d M).injective
  rw [cmp99SourceFlatQprimeAliasIndexOneVectorEquiv_reflection]
  apply (cmp89Eq245CenteredAliasVectorPiEquiv d M).injective
  funext mu
  change cmp99SourceCenteredAliasReflection M
      ⟨0, zero_mem_cmp89Eq245CenteredAliasIntegers
        (Nat.pos_of_ne_zero (NeZero.ne M))⟩ =
    ⟨0, zero_mem_cmp89Eq245CenteredAliasIntegers
      (Nat.pos_of_ne_zero (NeZero.ne M))⟩
  exact cmp99SourceCenteredAliasReflection_zero

/-- The central fine symbol is even in the base momentum. -/
theorem cmp89Eq249CentralEntireFineSymbol_neg
    (d M : ℕ) (mass : ℝ) (z : Fin d → ℂ) :
    cmp89Eq249CentralEntireFineSymbol d M 1 mass (-z) =
      cmp89Eq249CentralEntireFineSymbol d M 1 mass z := by
  unfold cmp89Eq249CentralEntireFineSymbol
  simpa only [pow_one] using
    cmp89Eq245EntireScaledLaplacianSymbol_neg
      d ((M : ℝ)⁻¹) mass z

/-- The central averaging pair is even because negation exchanges its two
entire factors. -/
theorem cmp89Eq249CentralEntireAveragePair_neg
    (d M : ℕ) (z : Fin d → ℂ) :
    cmp89Eq249CentralEntireAveragePair d M 1 (-z) =
      cmp89Eq249CentralEntireAveragePair d M 1 z := by
  unfold cmp89Eq249CentralEntireAveragePair cmp89Eq245EntireAveragePair
  simp only [pow_one, neg_neg]
  ring

/-- The complete noncentral rational alias sum is even after reindexing by
the actual half-open carrier reflection.  No literal integer negation is used. -/
theorem cmp89Eq249ComplexNoncentralAliasSum_neg
    (d M : ℕ) [NeZero M] (mass : ℝ) (z : Fin d → ℂ) :
    cmp89Eq249ComplexNoncentralAliasSum d M 1 mass (-z) =
      cmp89Eq249ComplexNoncentralAliasSum d M 1 mass z := by
  classical
  let central := cmp89Eq249CentralAliasIndex d M 1
  let reflect := cmp99SourceAliasIndexOneReflection d M
  let term := fun (w : Fin d → ℂ) (n : CMP89Eq246AliasIndex d M 1) =>
    cmp89Eq246EntireAliasAverageColumn d M 1 w n *
        cmp89Eq246EntireAliasAverageRow d M 1 w n /
      cmp89Eq246EntireAliasFineSymbol d M 1 mass w n
  have hreflectCentral : reflect central = central := by
    exact cmp99SourceAliasIndexOneReflection_central d M
  have hterm : ∀ n, term (-z) (reflect n) = term z n := by
    intro n
    simp only [term, reflect]
    rw [cmp89Eq246EntireAliasAverageColumn_neg_reflection_eq_row,
      cmp89Eq246EntireAliasAverageRow_neg_reflection_eq_column,
      cmp89Eq246EntireAliasFineSymbol_neg_reflection_eq]
    ring
  have hfull : (∑ n, term (-z) n) = ∑ n, term z n := by
    calc
      (∑ n, term (-z) n) = ∑ n, term (-z) (reflect n) := by
        exact (Equiv.sum_comp reflect (term (-z))).symm
      _ = ∑ n, term z n := by
        apply Finset.sum_congr rfl
        intro n _
        exact hterm n
  have hcentralTerm : term (-z) central = term z central := by
    have h := hterm central
    simpa only [hreflectCentral] using h
  rw [← cmp89Eq249AliasSubtypeNoncentralSum_eq d M 1 mass (-z),
    ← cmp89Eq249AliasSubtypeNoncentralSum_eq d M 1 mass z]
  have hleft := Finset.sum_erase_add Finset.univ (term (-z))
    (Finset.mem_univ central)
  have hright := Finset.sum_erase_add Finset.univ (term z)
    (Finset.mem_univ central)
  change (∑ n ∈ Finset.univ.erase central, term (-z) n) =
    ∑ n ∈ Finset.univ.erase central, term z n
  calc
    (∑ n ∈ Finset.univ.erase central, term (-z) n) =
        (∑ n, term (-z) n) - term (-z) central := by
      rw [← hleft]
      ring
    _ = (∑ n, term z n) - term z central := by
      rw [hfull, hcentralTerm]
    _ = ∑ n ∈ Finset.univ.erase central, term z n := by
      rw [← hright]
      ring

/-- The central-stabilized denominator is even after the complete noncentral
alias sum is reindexed. -/
theorem cmp89Eq249CentralStabilizedAliasDenominator_neg
    (d M : ℕ) [NeZero M] (mass a : ℝ) (z : Fin d → ℂ) :
    cmp89Eq249CentralStabilizedAliasDenominator d M 1 mass a (-z) =
      cmp89Eq249CentralStabilizedAliasDenominator d M 1 mass a z := by
  unfold cmp89Eq249CentralStabilizedAliasDenominator
  rw [cmp89Eq249CentralEntireFineSymbol_neg,
    cmp89Eq249CentralEntireAveragePair_neg,
    cmp89Eq249ComplexNoncentralAliasSum_neg]

/-- Reflection transports the stabilized transposed solution at opposite
momentum to the stabilized column solution at direct momentum. -/
theorem cmp89Eq249StabilizedAliasTransposeSolution_neg_reflection_eq_column
    (d M : ℕ) [NeZero M] (mass a : ℝ) (z : Fin d → ℂ)
    (m : CMP89Eq246AliasIndex d M 1) :
    cmp89Eq249StabilizedAliasTransposeSolution d M 1 mass a (-z)
        (cmp99SourceAliasIndexOneReflection d M m) =
      cmp89Eq249StabilizedAliasColumnSolution d M 1 mass a z m := by
  classical
  let central := cmp89Eq249CentralAliasIndex d M 1
  let reflect := cmp99SourceAliasIndexOneReflection d M
  by_cases hm : m = central
  · subst m
    rw [show reflect central = central by
      exact cmp99SourceAliasIndexOneReflection_central d M]
    rw [cmp89Eq249StabilizedAliasTransposeSolution_central,
      cmp89Eq249StabilizedAliasColumnSolution_central]
    have hrow :=
      cmp89Eq246EntireAliasAverageRow_neg_reflection_eq_column
        (d := d) (M := M) z central
    rw [cmp99SourceAliasIndexOneReflection_central] at hrow
    rw [hrow, cmp89Eq249CentralStabilizedAliasDenominator_neg]
  · have hreflectNe : reflect m ≠ central := by
      intro h
      apply hm
      apply reflect.injective
      rw [h]
      exact (cmp99SourceAliasIndexOneReflection_central d M).symm
    rw [cmp89Eq249StabilizedAliasTransposeSolution_noncentral
        d M 1 mass a (-z) (reflect m) hreflectNe,
      cmp89Eq249StabilizedAliasColumnSolution_noncentral
        d M 1 mass a z m hm]
    rw [cmp89Eq249CentralEntireFineSymbol_neg,
      cmp89Eq246EntireAliasAverageRow_neg_reflection_eq_column,
      cmp89Eq246EntireAliasFineSymbol_neg_reflection_eq,
      cmp89Eq249CentralStabilizedAliasDenominator_neg]

end

end YangMills.RG
