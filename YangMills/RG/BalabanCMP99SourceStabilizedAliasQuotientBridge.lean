/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceAliasReflectionStabilizedSolution
import YangMills.RG.BalabanCMP89Eq248ComplexAliasDenominatorPeriodicity

/-!
# Stabilized-to-quotient bridge for the physical orientation transport

PRE-VALIDATION: this source is present, its `.olean` has not yet been
materialized, and its declarations have not yet been compiler verified.

Away from the removable central zero, the stabilized row and column
solutions must reduce to the literal rational solutions.  This module proves
that cancellation rather than assuming it.  It also proves evenness and
coordinatewise physical periodicity of the reduced denominator itself.  In
particular it does not claim periodicity of the central-stabilized
denominator.

The affine cross-fibre carry, the zero coarse fibre, endpoint phases, the
complete physical finite sum, Brillouin periodization, regional `B0`, window
15, terminal fields and `TermSource` remain open.
-/

namespace YangMills.RG

noncomputable section

/-- The complete reduced denominator is even after reindexing the actual
half-open centered alias carrier. -/
theorem cmp89Eq247ComplexReducedAliasDenominator_neg
    (d M : ℕ) [NeZero M] (mass a : ℝ) (z : Fin d → ℂ) :
    cmp89Eq247ComplexReducedAliasDenominator d M 1 mass a (-z) =
      cmp89Eq247ComplexReducedAliasDenominator d M 1 mass a z := by
  classical
  let aliases := cmp89Eq245CenteredAliasVectors d (M ^ 1)
  let reflect := cmp99SourceAliasIndexOneReflection d M
  let term := fun (w : Fin d → ℂ) (n : CMP89Eq246AliasIndex d M 1) =>
    cmp89Eq246EntireAliasAverageColumn d M 1 w n *
        cmp89Eq246EntireAliasAverageRow d M 1 w n /
      cmp89Eq246EntireAliasFineSymbol d M 1 mass w n
  have hterm : ∀ n, term (-z) (reflect n) = term z n := by
    intro n
    simp only [term, reflect]
    rw [cmp89Eq246EntireAliasAverageColumn_neg_reflection_eq_row,
      cmp89Eq246EntireAliasAverageRow_neg_reflection_eq_column,
      cmp89Eq246EntireAliasFineSymbol_neg_reflection_eq]
    ring
  have hsum : (∑ n, term (-z) n) = ∑ n, term z n := by
    calc
      (∑ n, term (-z) n) = ∑ n, term (-z) (reflect n) := by
        exact (Equiv.sum_comp reflect (term (-z))).symm
      _ = ∑ n, term z n := by
        apply Finset.sum_congr rfl
        intro n _
        exact hterm n
  have hraw (w : Fin d → ℂ) :
      (∑ n : CMP89Eq246AliasIndex d M 1, term w n) =
        ∑ m ∈ aliases,
          cmp89Eq248ComplexAliasDenominatorSummand d M 1 mass w m := by
    rw [Finset.sum_subtype aliases (fun _ => Iff.rfl)]
    apply Finset.sum_congr rfl
    intro m _
    rfl
  rw [cmp89Eq247ComplexReducedAliasDenominator]
  change 1 + (a : ℂ) *
      (∑ m ∈ aliases,
        cmp89Eq248ComplexAliasDenominatorSummand d M 1 mass (-z) m) =
    1 + (a : ℂ) *
      (∑ m ∈ aliases,
        cmp89Eq248ComplexAliasDenominatorSummand d M 1 mass z m)
  rw [← hraw (-z), ← hraw z, hsum]

/-- Coordinatewise integer physical periods preserve the reduced denominator.
The proof composes the already sealed one-coordinate period and does not
promote the stabilized denominator to a periodic object. -/
theorem cmp89Eq247ComplexReducedAliasDenominator_add_intPeriods
    {d L j : ℕ} [NeZero L] (mass a : ℝ) (z : Fin d → ℂ)
    (w : Fin d → ℤ) :
    cmp89Eq247ComplexReducedAliasDenominator d L j mass a
        (fun mu => z mu + (w mu : ℂ) * (2 * Real.pi : ℂ)) =
      cmp89Eq247ComplexReducedAliasDenominator d L j mass a z := by
  classical
  let F : (Fin d → ℂ) → ℂ := fun q =>
    cmp89Eq247ComplexReducedAliasDenominator d L j mass a q
  have hcoordinate : ∀ mu,
      Function.Periodic F (Pi.single mu (2 * Real.pi : ℂ)) := by
    intro mu q
    simpa [F, cmp89Eq248PhysicalCoordinatePeriodShift] using
      (cmp89Eq247ComplexReducedAliasDenominator_physicalPeriodShift
        (d := d) (L := L) (j := j) mass a mu q)
  have hsum : Function.Periodic F
      (∑ mu : Fin d, (w mu) • Pi.single mu (2 * Real.pi : ℂ)) := by
    induction (Finset.univ : Finset (Fin d)) using Finset.induction_on with
    | empty => simp [Function.Periodic]
    | @insert mu s hmu ih =>
        rw [Finset.sum_insert hmu]
        exact ((hcoordinate mu).zsmul (w mu)).add_period ih
  have hperiod := hsum z
  have hvector :
      z + (∑ mu : Fin d, (w mu) • Pi.single mu (2 * Real.pi : ℂ)) =
        fun mu => z mu + (w mu : ℂ) * (2 * Real.pi : ℂ) := by
    funext mu
    simp [Pi.single_apply, zsmul_eq_mul]
  rw [hvector] at hperiod
  exact hperiod

/-- Literal direct-column rational solution before central stabilization. -/
def cmp89Eq247EntireAliasColumnSolution
    (d L j : ℕ) (mass a : ℝ) (z : Fin d → ℂ) :
    CMP89Eq246AliasIndex d L j → ℂ :=
  fun m =>
    cmp89Eq246EntireAliasAverageColumn d L j z m /
      (cmp89Eq246EntireAliasFineSymbol d L j mass z m *
        cmp89Eq247ComplexReducedAliasDenominator d L j mass a z)

/-- On the complete non-singular domain, central stabilization of the row
solution cancels exactly to the printed rational solution. -/
theorem cmp89Eq249StabilizedAliasTransposeSolution_eq_unstabilized
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin d → ℂ)
    (hfine : ∀ m : CMP89Eq246AliasIndex d L j,
      cmp89Eq246EntireAliasFineSymbol d L j mass z m ≠ 0)
    (hreduced :
      cmp89Eq247ComplexReducedAliasDenominator d L j mass a z ≠ 0) :
    cmp89Eq249StabilizedAliasTransposeSolution d L j mass a z =
      cmp89Eq247EntireAliasTransposeSolution d L j mass a z := by
  funext m
  let central := cmp89Eq249CentralAliasIndex d L j
  let centralFine := cmp89Eq249CentralEntireFineSymbol d L j mass z
  have hcentralValue :
      cmp89Eq246EntireAliasFineSymbol d L j mass z central = centralFine := by
    simp [central, centralFine, cmp89Eq246EntireAliasFineSymbol,
      cmp89Eq249CentralEntireFineSymbol, cmp89Eq248EntireAliasMomentum_zero]
  have hcentral : centralFine ≠ 0 := by
    rw [← hcentralValue]
    exact hfine central
  have hstabilized :=
    cmp89Eq249CentralFine_mul_reduced_eq_stabilized
      d L j mass a z hcentral
  by_cases hm : m = central
  · subst m
    rw [cmp89Eq249StabilizedAliasTransposeSolution_central]
    unfold cmp89Eq247EntireAliasTransposeSolution
    rw [hcentralValue, hstabilized]
  · rw [cmp89Eq249StabilizedAliasTransposeSolution_noncentral
      d L j mass a z m hm]
    unfold cmp89Eq247EntireAliasTransposeSolution
    rw [← hstabilized]
    field_simp [hcentral, hfine m, hreduced]
    change _ * centralFine / centralFine = _
    field_simp [hcentral]

/-- On the same non-singular domain, the separately constructed stabilized
column solution cancels to its literal rational quotient. -/
theorem cmp89Eq249StabilizedAliasColumnSolution_eq_unstabilized
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin d → ℂ)
    (hfine : ∀ m : CMP89Eq246AliasIndex d L j,
      cmp89Eq246EntireAliasFineSymbol d L j mass z m ≠ 0)
    (hreduced :
      cmp89Eq247ComplexReducedAliasDenominator d L j mass a z ≠ 0) :
    cmp89Eq249StabilizedAliasColumnSolution d L j mass a z =
      cmp89Eq247EntireAliasColumnSolution d L j mass a z := by
  funext m
  let central := cmp89Eq249CentralAliasIndex d L j
  let centralFine := cmp89Eq249CentralEntireFineSymbol d L j mass z
  have hcentralValue :
      cmp89Eq246EntireAliasFineSymbol d L j mass z central = centralFine := by
    simp [central, centralFine, cmp89Eq246EntireAliasFineSymbol,
      cmp89Eq249CentralEntireFineSymbol, cmp89Eq248EntireAliasMomentum_zero]
  have hcentral : centralFine ≠ 0 := by
    rw [← hcentralValue]
    exact hfine central
  have hstabilized :=
    cmp89Eq249CentralFine_mul_reduced_eq_stabilized
      d L j mass a z hcentral
  by_cases hm : m = central
  · subst m
    rw [cmp89Eq249StabilizedAliasColumnSolution_central]
    unfold cmp89Eq247EntireAliasColumnSolution
    rw [hcentralValue, hstabilized]
  · rw [cmp89Eq249StabilizedAliasColumnSolution_noncentral
      d L j mass a z m hm]
    unfold cmp89Eq247EntireAliasColumnSolution
    rw [← hstabilized]
    field_simp [hcentral, hfine m, hreduced]
    change _ * centralFine / centralFine = _
    field_simp [hcentral]

end

end YangMills.RG
