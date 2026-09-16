import YangMills.RG.BalabanCMP99SourceFlatQprimePhysicalStabilizedAliasTransposeFullSolution

/-!
# PRE-VALIDATION: scalar linearity of the arbitrary-source transpose solution

Source is present, its promoted `.olean` has not yet been materialized, and
the result has not yet been compiler-verified.

This is algebraic infrastructure for the physical full-G point-source
dictionary. It does not identify a physical Green, assert a decay bound,
attain window 15, discharge a terminal field or inhabit `TermSource`.
-/

namespace YangMills.RG

open Matrix

noncomputable section

/-- The noncentral source moment is linear under a common scalar multiplier. -/
theorem cmp89Eq246StabilizedAliasTransposeNoncentralSourceMoment_mul_right
    (d L j : ℕ) [NeZero L] (mass : ℝ) (z : Fin d → ℂ)
    (source : CMP89Eq246AliasIndex d L j → ℂ) (c : ℂ) :
    cmp89Eq246StabilizedAliasTransposeNoncentralSourceMoment
        d L j mass z (fun n => source n * c) =
      cmp89Eq246StabilizedAliasTransposeNoncentralSourceMoment
        d L j mass z source * c := by
  classical
  unfold cmp89Eq246StabilizedAliasTransposeNoncentralSourceMoment
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- The exact central source moment is linear under a common scalar multiplier. -/
theorem cmp89Eq246StabilizedAliasTransposeFullSolutionMoment_mul_right
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin d → ℂ)
    (source : CMP89Eq246AliasIndex d L j → ℂ) (c : ℂ) :
    cmp89Eq246StabilizedAliasTransposeFullSolutionMoment
        d L j mass a z (fun n => source n * c) =
      cmp89Eq246StabilizedAliasTransposeFullSolutionMoment
        d L j mass a z source * c := by
  classical
  unfold cmp89Eq246StabilizedAliasTransposeFullSolutionMoment
  rw [cmp89Eq246StabilizedAliasTransposeNoncentralSourceMoment_mul_right]
  ring

/-- Every output coordinate of the explicit transpose solution is linear in
the arbitrary source. The statement is pointwise so later consumers cannot
smuggle in an operator-level inverse or self-adjointness assumption. -/
theorem cmp89Eq246StabilizedAliasTransposeFullSolution_mul_right
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin d → ℂ)
    (source : CMP89Eq246AliasIndex d L j → ℂ) (c : ℂ)
    (m : CMP89Eq246AliasIndex d L j) :
    cmp89Eq246StabilizedAliasTransposeFullSolution
        d L j mass a z (fun n => source n * c) m =
      cmp89Eq246StabilizedAliasTransposeFullSolution
        d L j mass a z source m * c := by
  classical
  let central := cmp89Eq249CentralAliasIndex d L j
  let fine := cmp89Eq246EntireAliasFineSymbol d L j mass z
  let column := cmp89Eq246EntireAliasAverageColumn d L j z
  let row := cmp89Eq246EntireAliasAverageRow d L j z
  let moment :=
    cmp89Eq246StabilizedAliasTransposeFullSolutionMoment
      d L j mass a z source
  have hmoment :
      cmp89Eq246StabilizedAliasTransposeFullSolutionMoment
          d L j mass a z (fun n => source n * c) = moment * c := by
    simpa only [moment] using
      cmp89Eq246StabilizedAliasTransposeFullSolutionMoment_mul_right
        d L j mass a z source c
  by_cases hm : m = central
  · have hsum :
        (∑ n ∈ Finset.univ.erase central,
            column n *
              (source n * c / fine n -
                (a : ℂ) * row n * (moment * c) / fine n)) =
          (∑ n ∈ Finset.univ.erase central,
              column n *
                (source n / fine n -
                  (a : ℂ) * row n * moment / fine n)) * c := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n _
      ring
    simp only [cmp89Eq246StabilizedAliasTransposeFullSolution,
      central, fine, column, row, moment, hm, if_pos]
    rw [hmoment, hsum]
    ring
  · simp only [cmp89Eq246StabilizedAliasTransposeFullSolution,
      central, fine, column, row, moment, hm, if_false]
    rw [hmoment]
    ring

end

end YangMills.RG
