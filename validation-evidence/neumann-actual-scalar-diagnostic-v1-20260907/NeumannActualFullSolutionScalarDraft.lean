import YangMills.RG.BalabanCMP89Eq246StabilizedAliasFullSolution

/-!
# PRE-VALIDATION: scalar homogeneity of the literal (2.46) solution

Source present; .olean not materialized; result not compiler-verified.
This is the non-transpose solution consumed by FinePointSourceFibreGreen.
No invertibility, nonvanishing or Green covariance is assumed. Totalized
division permits this algebraic identity even at singular parameters;
that does NOT claim that the formula is an inverse there.
The endpoint phase and common block translation remain separate obligations.
-/

namespace YangMills.RG
noncomputable section

theorem neumannActualNoncentralSourceMoment_mul_right
    (d L j : ℕ) [NeZero L] (mass : ℝ) (z : Fin d → ℂ)
    (source : CMP89Eq246AliasIndex d L j → ℂ) (c : ℂ) :
    cmp89Eq246StabilizedAliasNoncentralSourceMoment
        d L j mass z (fun n => source n * c) =
      cmp89Eq246StabilizedAliasNoncentralSourceMoment d L j mass z source * c := by
  classical
  unfold cmp89Eq246StabilizedAliasNoncentralSourceMoment
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem neumannActualFullSolutionMoment_mul_right
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin d → ℂ)
    (source : CMP89Eq246AliasIndex d L j → ℂ) (c : ℂ) :
    cmp89Eq246StabilizedAliasFullSolutionMoment
        d L j mass a z (fun n => source n * c) =
      cmp89Eq246StabilizedAliasFullSolutionMoment d L j mass a z source * c := by
  classical
  unfold cmp89Eq246StabilizedAliasFullSolutionMoment
  rw [neumannActualNoncentralSourceMoment_mul_right]
  ring

theorem neumannActualFullSolution_mul_right
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin d → ℂ)
    (source : CMP89Eq246AliasIndex d L j → ℂ) (c : ℂ)
    (m : CMP89Eq246AliasIndex d L j) :
    cmp89Eq246StabilizedAliasFullSolution
        d L j mass a z (fun n => source n * c) m =
      cmp89Eq246StabilizedAliasFullSolution d L j mass a z source m * c := by
  classical
  let central := cmp89Eq249CentralAliasIndex d L j
  let fine := cmp89Eq246EntireAliasFineSymbol d L j mass z
  let column := cmp89Eq246EntireAliasAverageColumn d L j z
  let row := cmp89Eq246EntireAliasAverageRow d L j z
  let moment := cmp89Eq246StabilizedAliasFullSolutionMoment d L j mass a z source
  have hmoment : cmp89Eq246StabilizedAliasFullSolutionMoment
      d L j mass a z (fun n => source n * c) = moment * c := by
    exact neumannActualFullSolutionMoment_mul_right d L j mass a z source c
  have hsum :
      (∑ n ∈ Finset.univ.erase central,
        row n * (source n * c / fine n -
          (a : ℂ) * column n * (moment * c) / fine n)) =
      (∑ n ∈ Finset.univ.erase central,
        row n * (source n / fine n -
          (a : ℂ) * column n * moment / fine n)) * c := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n _
    ring
  by_cases hm : m = central
  · simp only [cmp89Eq246StabilizedAliasFullSolution,
      central, fine, column, row, moment, hm, if_pos]
    rw [hmoment, hsum]
    ring
  · simp only [cmp89Eq246StabilizedAliasFullSolution,
      central, fine, column, row, moment, hm, if_false]
    rw [hmoment]
    ring

#print axioms neumannActualNoncentralSourceMoment_mul_right
#print axioms neumannActualFullSolutionMoment_mul_right
#print axioms neumannActualFullSolution_mul_right

end
end YangMills.RG
